import argparse
import mimetypes
import os
import posixpath
import re
import time
import xml.etree.ElementTree as ET
from collections import deque
from urllib.parse import parse_qsl, unquote, urljoin, urlsplit, urlunsplit

import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

USER_AGENT = 'WordPress2Static/1.0'
REQUEST_TIMEOUT = 30

EXCLUDED_PATH_PATTERNS = [re.compile(pattern) for pattern in (
    r'^/wp-admin(/|$)',
    r'^/wp-login\.php',
    r'^/wp-cron\.php',
    r'^/xmlrpc\.php',
    r'^/wp-json(/|$)',
    r'^/wp-sitemap',
    r'(^|/)feed(/|$)',
    r'(^|/)trackback(/|$)',
    r'(^|/)embed(/|$)',
)]

EXCLUDED_QUERY_KEYS = {'s', 'replytocom', 'share', 'like_comment', 'preview', 'rest_route', 'feed', 'doing_wp_cron'}

SKIPPED_LINK_RELS = {'pingback', 'edituri', 'wlwmanifest', 'shortlink', 'dns-prefetch', 'preconnect',
                     'https://api.w.org/', 'alternate'}

URL_ATTRIBUTES = {
    'a': ('href',),
    'area': ('href',),
    'link': ('href',),
    'script': ('src',),
    'img': ('src', 'data-src', 'data-lazy-src'),
    'source': ('src', 'data-src'),
    'video': ('src', 'poster'),
    'audio': ('src',),
    'track': ('src',),
    'iframe': ('src',),
    'embed': ('src',),
    'object': ('data',),
    'input': ('src',),
}
SRCSET_ATTRIBUTES = ('srcset', 'data-srcset', 'data-lazy-srcset')

CSS_URL_RE = re.compile(r'''url\(\s*(?P<quote>['"]?)(?P<url>[^'")]*?)(?P=quote)\s*\)''', re.IGNORECASE)
CSS_IMPORT_RE = re.compile(r'''@import\s+(?P<quote>['"])(?P<url>[^'"]+)(?P=quote)''', re.IGNORECASE)

NON_FETCHABLE_PREFIXES = ('#', 'data:', 'mailto:', 'tel:', 'javascript:', 'about:')

WP_CONTENT_URL_RE = re.compile(
    r'''(?:https?:)?(?:\\?/){2}[A-Za-z0-9.-]+(?::\d+)?(?:\\?/[^\s"'`<>()\\/]*)*?\\?/wp-content\\?/[^\s"'`<>()]*''',
    re.IGNORECASE)


def sanitize_segment(segment):
    return re.sub(r'[<>:"\\|?*\x00-\x1f]', '_', segment)


def sanitize_query(query):
    return re.sub(r'[^A-Za-z0-9._-]+', '-', query).strip('-')[:100]


def iter_srcset(value):
    for candidate in value.split(','):
        parts = candidate.strip().split(None, 1)
        if parts:
            yield parts[0], parts[1] if len(parts) > 1 else ''


class SiteExporter:
    def __init__(self, base_url, output_folder_path, delay, strip_index_html=False, aliases=()):
        split = urlsplit(base_url)
        if split.scheme not in ('http', 'https') or not split.hostname:
            raise ValueError(f'Invalid base URL: {base_url}')

        self.scheme = split.scheme
        self.netloc = split.netloc.lower()
        self.host = self.strip_www(split.hostname.lower())
        self.port = split.port
        self.hosts = {self.host} | {self.strip_www(alias.lower()) for alias in aliases}
        self.base_path = split.path.rstrip('/') + '/'
        self.root_url = urlunsplit((self.scheme, self.netloc, self.base_path, '', ''))

        self.output_folder_path = os.path.abspath(output_folder_path)
        self.delay = delay
        self.strip_index_html = strip_index_html

        self.session = requests.Session()
        self.session.headers['User-Agent'] = USER_AGENT
        retry = Retry(total=3, backoff_factor=1, status_forcelist=(429, 500, 502, 503, 504))
        self.session.mount('http://', HTTPAdapter(max_retries=retry))
        self.session.mount('https://', HTTPAdapter(max_retries=retry))

        self.queue = deque()
        self.seen = set()
        self.local_paths = {}
        self.html_documents = []
        self.css_documents = []
        self.binary_count = 0
        self.failures = []

    @staticmethod
    def strip_www(host):
        return host[4:] if host.startswith('www.') else host

    def normalize(self, url):
        split = urlsplit(url)
        if split.scheme not in ('http', 'https') or not split.hostname:
            return None
        hostname = self.strip_www(split.hostname.lower())
        if hostname not in self.hosts or (hostname == self.host and split.port != self.port):
            return None

        path = split.path or '/'
        if not path.startswith(self.base_path) and path + '/' != self.base_path:
            return None

        return urlunsplit((self.scheme, self.netloc, path, split.query, ''))

    def site_relative_path(self, url):
        path = urlsplit(url).path
        return '/' + path[len(self.base_path):] if path.startswith(self.base_path) else '/'

    def is_wp_content(self, url):
        return self.site_relative_path(url).startswith('/wp-content/')

    def is_excluded(self, url):
        path = self.site_relative_path(url)
        if any(pattern.search(path) for pattern in EXCLUDED_PATH_PATTERNS):
            return True
        query_keys = {key for key, _ in parse_qsl(urlsplit(url).query, keep_blank_values=True)}
        return bool(query_keys & EXCLUDED_QUERY_KEYS)

    @staticmethod
    def resolve(base_url, raw_url):
        raw_url = (raw_url or '').strip()
        if not raw_url or raw_url.lower().startswith(NON_FETCHABLE_PREFIXES):
            return None
        return urljoin(base_url, raw_url)

    def enqueue(self, url):
        normalized = self.normalize(url) if url else None
        if normalized and normalized not in self.seen and not self.is_excluded(normalized):
            self.seen.add(normalized)
            self.queue.append(normalized)

    def local_path_for(self, url, content_type, is_html):
        split = urlsplit(url)
        relative = unquote(self.site_relative_path(url))
        segments = [sanitize_segment(s) for s in relative.split('/') if s not in ('', '.', '..')]
        is_directory = relative.endswith('/') or not segments
        query_suffix = '-' + sanitize_query(split.query) if split.query else ''

        if is_html:
            if not is_directory and segments[-1].lower().endswith(('.html', '.htm')):
                name, extension = posixpath.splitext(segments[-1])
                segments[-1] = name + query_suffix + extension
            else:
                segments.append('index' + query_suffix + '.html')
        else:
            if is_directory:
                segments.append('index')
            name, extension = posixpath.splitext(segments[-1])
            if not extension or extension.lower() == '.php':
                name += query_suffix
                extension = mimetypes.guess_extension(content_type) or ''
            segments[-1] = name + extension

        return '/'.join(segments)

    def relative_link(self, from_local_path, base_url, raw_url):
        resolved = self.resolve(base_url, raw_url)
        normalized = self.normalize(resolved) if resolved else None
        target = self.local_paths.get(normalized)
        if target is None and normalized and self.is_wp_content(normalized):
            path = urlsplit(normalized).path
            target = self.local_path_for(normalized, mimetypes.guess_type(path)[0] or '', path.lower().endswith(('.html', '.htm')))
        if target is None:
            return None

        from_directory = '/' + posixpath.dirname(from_local_path)
        if self.strip_index_html and posixpath.basename(target) == 'index.html':
            relative = posixpath.relpath('/' + posixpath.dirname(target), from_directory)
            relative = './' if relative == '.' else relative + '/'
        else:
            relative = posixpath.relpath('/' + target, from_directory)
        fragment = urlsplit(resolved).fragment
        return relative + ('#' + fragment if fragment else '')

    def load_sitemap(self, sitemap_url, visited=None):
        visited = visited if visited is not None else set()
        if sitemap_url in visited:
            return
        visited.add(sitemap_url)

        try:
            response = self.session.get(sitemap_url, timeout=REQUEST_TIMEOUT)
            response.raise_for_status()
            root = ET.fromstring(response.content)
        except (requests.RequestException, ET.ParseError) as error:
            print(f'Could not read sitemap {sitemap_url}: {error}')
            return

        locations = [element.text.strip() for element in root.iter()
                     if element.tag.endswith('loc') and element.text]
        if root.tag.endswith('sitemapindex'):
            for location in locations:
                self.load_sitemap(location, visited)
        else:
            print(f'Sitemap {sitemap_url}: {len(locations)} URLs')
            for location in locations:
                self.enqueue(location)

    def crawl(self):
        self.enqueue(self.root_url)
        self.load_sitemap(urljoin(self.root_url, 'wp-sitemap.xml'))

        count = 0
        while self.queue:
            url = self.queue.popleft()
            count += 1
            print(f'[{count}, {len(self.queue)} queued] {url}')
            self.fetch(url)
            if self.delay:
                time.sleep(self.delay)

    def fetch(self, url):
        if url in self.local_paths:
            return

        try:
            response = self.session.get(url, timeout=REQUEST_TIMEOUT)
        except requests.RequestException as error:
            self.failures.append((url, str(error)))
            return
        if response.status_code != 200:
            self.failures.append((url, f'HTTP {response.status_code}'))
            return

        final_url = self.normalize(response.url)
        if final_url is None:
            self.failures.append((url, f'redirects off-site to {response.url}'))
            return
        if final_url in self.local_paths:
            self.local_paths[url] = self.local_paths[final_url]
            return
        self.seen.add(final_url)

        content_type = response.headers.get('Content-Type', '').split(';')[0].strip().lower()
        path = urlsplit(final_url).path.lower()
        is_html = 'html' in content_type
        is_css = content_type == 'text/css' or (not is_html and path.endswith('.css'))
        local_path = self.local_path_for(final_url, content_type, is_html)

        if is_html:
            soup = BeautifulSoup(response.content, 'html.parser')
            self.discover_html_links(final_url, soup)
            self.html_documents.append((final_url, local_path, soup))
        elif is_css:
            text, encoding = self.decode(response.content)
            self.discover_css_links(final_url, text)
            self.css_documents.append((final_url, local_path, text, encoding))
        else:
            self.write_file(local_path, response.content)
            self.binary_count += 1

        self.local_paths[final_url] = local_path
        self.local_paths[url] = local_path

    @staticmethod
    def decode(content):
        for encoding in ('utf-8', 'latin-1'):
            try:
                return content.decode(encoding), encoding
            except UnicodeDecodeError:
                continue

    def discover_html_links(self, page_url, soup):
        for tag in soup.find_all(True):
            if tag.name == 'link' and {rel.lower() for rel in tag.get('rel', [])} & SKIPPED_LINK_RELS:
                continue
            for attribute in URL_ATTRIBUTES.get(tag.name, ()):
                if tag.has_attr(attribute):
                    self.enqueue(self.resolve(page_url, tag[attribute]))
            for attribute in SRCSET_ATTRIBUTES:
                if tag.has_attr(attribute) and not tag[attribute].lstrip().startswith('data:'):
                    for url, _ in iter_srcset(tag[attribute]):
                        self.enqueue(self.resolve(page_url, url))
            if tag.has_attr('style'):
                self.discover_css_links(page_url, tag['style'])
            if tag.name == 'style' and tag.string:
                self.discover_css_links(page_url, tag.string)
            for attribute in self.free_text_attributes(tag):
                self.discover_wp_content_links(page_url, tag[attribute])
        for string in soup.find_all(string=True):
            if 'wp-content' in string:
                self.discover_wp_content_links(page_url, string)

    @staticmethod
    def free_text_attributes(tag):
        handled = set(URL_ATTRIBUTES.get(tag.name, ())) | set(SRCSET_ATTRIBUTES)
        return [attribute for attribute, value in tag.attrs.items()
                if attribute not in handled and isinstance(value, str) and 'wp-content' in value]

    def discover_wp_content_links(self, base_url, text):
        for match in WP_CONTENT_URL_RE.finditer(text):
            self.enqueue(self.resolve(base_url, match.group(0).replace('\\/', '/').rstrip('\\')))

    def discover_css_links(self, base_url, css_text):
        for regex in (CSS_URL_RE, CSS_IMPORT_RE):
            for match in regex.finditer(css_text):
                self.enqueue(self.resolve(base_url, match.group('url')))

    def rewrite_css(self, css_text, base_url, local_path):
        def replace(match):
            new_url = self.relative_link(local_path, base_url, match.group('url'))
            if new_url is None:
                return match.group(0)
            start, end = match.span('url')
            whole_start = match.start()
            text = match.group(0)
            return text[:start - whole_start] + new_url + text[end - whole_start:]

        return CSS_IMPORT_RE.sub(replace, CSS_URL_RE.sub(replace, css_text))

    def rewrite_wp_content_links(self, text, base_url, local_path):
        def replace(match):
            raw = match.group(0)
            trailing = raw[len(raw.rstrip('\\')):]
            raw = raw[:len(raw) - len(trailing)]
            escaped = '\\/' in raw
            new_url = self.relative_link(local_path, base_url, raw.replace('\\/', '/'))
            if new_url is None:
                return match.group(0)
            return (new_url.replace('/', '\\/') if escaped else new_url) + trailing

        return WP_CONTENT_URL_RE.sub(replace, text)

    def rewrite_html(self, page_url, local_path, soup):
        for tag in soup.find_all(True):
            for attribute in URL_ATTRIBUTES.get(tag.name, ()):
                if tag.has_attr(attribute):
                    new_url = self.relative_link(local_path, page_url, tag[attribute])
                    if new_url is not None:
                        tag[attribute] = new_url
            for attribute in SRCSET_ATTRIBUTES:
                if tag.has_attr(attribute) and not tag[attribute].lstrip().startswith('data:'):
                    candidates = []
                    for url, descriptor in iter_srcset(tag[attribute]):
                        new_url = self.relative_link(local_path, page_url, url) or url
                        candidates.append(f'{new_url} {descriptor}'.strip())
                    tag[attribute] = ', '.join(candidates)
            if tag.has_attr('style'):
                tag['style'] = self.rewrite_css(tag['style'], page_url, local_path)
            if tag.name == 'style' and tag.string:
                tag.string = self.rewrite_css(tag.string, page_url, local_path)
            for attribute in self.free_text_attributes(tag):
                tag[attribute] = self.rewrite_wp_content_links(tag[attribute], page_url, local_path)
        for string in soup.find_all(string=True):
            if 'wp-content' in string:
                new_text = self.rewrite_wp_content_links(string, page_url, local_path)
                if new_text != string:
                    string.replace_with(type(string)(new_text))

    def write_file(self, local_path, content):
        full_path = os.path.join(self.output_folder_path, *local_path.split('/'))
        if os.path.commonpath([self.output_folder_path, os.path.abspath(full_path)]) != self.output_folder_path:
            raise ValueError(f'Refusing to write outside the output folder: {local_path}')
        os.makedirs(os.path.dirname(full_path), exist_ok=True)
        with open(full_path, 'wb') as file:
            file.write(content)

    def write_documents(self):
        for url, local_path, soup in self.html_documents:
            self.rewrite_html(url, local_path, soup)
            self.write_file(local_path, soup.encode('utf-8'))
        for url, local_path, text, encoding in self.css_documents:
            self.write_file(local_path, self.rewrite_css(text, url, local_path).encode(encoding))

    def export(self):
        os.makedirs(self.output_folder_path, exist_ok=True)
        self.crawl()
        self.write_documents()

        print()
        print(f'Exported to {self.output_folder_path}')
        print(f'  HTML pages:  {len(self.html_documents)}')
        print(f'  CSS files:   {len(self.css_documents)}')
        print(f'  Other files: {self.binary_count}')
        if self.failures:
            print(f'  Failed:      {len(self.failures)}')
            for url, reason in self.failures:
                print(f'    {url} ({reason})')


def main():
    parser = argparse.ArgumentParser(description='WordPress 2 Static')
    parser.add_argument('url', type=str, help='Base URL: https://my-website.com')
    parser.add_argument('output_folder_path', type=str, help='Output folder path: ./output')
    parser.add_argument('--delay', type=float, default=0.1, help='Seconds to wait between requests (default: 0.1)')
    parser.add_argument('--strip-index-html', action='store_true',
                        help='Link to directories ("about/") instead of "about/index.html". '
                             'Requires a web server; links will not work when opening files from disk.')
    parser.add_argument('--alias', action='append', default=[], metavar='HOST',
                        help='Another host name that serves the same site (e.g. an old development domain). '
                             'Links to it are exported and made relative. Can be given more than once.')

    args = parser.parse_args()
    url = args.url
    output_folder_path = args.output_folder_path

    SiteExporter(url, output_folder_path, args.delay, args.strip_index_html, args.alias).export()


if __name__ == "__main__":
    main()
