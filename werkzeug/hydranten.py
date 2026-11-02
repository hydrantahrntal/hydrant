#!/usr/bin/env python3
"""Hydranten-Quelle für die Relaisleitung

Lädt OpenStreetMap-Auszüge von Geofabrik, filtert Hydranten, Saugstellen,
Löschwasserbehälter und Löschteiche heraus und schreibt sie als Kacheln
für GitHub Pages:

  index.json        Stand, Anzahl, Kachelliste mit Abdeckung je Rasterzelle
  k/<i>_<j>.json    Einträge einer Kachel (0,25° × 0,25°) im Overpass-Format
  km/<i>_<j>.json   Kilometersteine (highway=milestone) derselben Kachel
  index.html        kurze Übersicht zum Nachschauen im Browser

Kilometersteine (seit 11/2026, für die Karte im Whiteboard): je Kachel
{"km": [[Breite, Länge, Kilometer, Straße, Id, Quelle], …]}. Kilometer ist eine
Zahl (22.5), Straße die Straßennummer ohne Leerzeichen und Punkte (z. B.
"SS621"). Quelle "bz" = Straßendienst des Landes Südtirol (Datensatz
"Kilometersteine – Cippi chilometrici", CC0, WFS p_bz-TransportNetwork:
Signs-Milestones; nur Staats-/Landesstraßen und Autobahn), "osm" =
OpenStreetMap (highway=milestone; Straße = Nummer der Straße, auf der der Stein
als Punkt liegt, sonst die Angabe am Stein). Wo das Land einen Stein hat, fallen
OSM-Steine mit demselben Kilometer im Umkreis von 300 m weg. In index.json steht
unter "km" die Anzahl je Kachel; die Abdeckung ("c") gilt wie für Hydranten.

Kachel i_j deckt Breite i·0,25 … (i+1)·0,25 und Länge j·0,25 … (j+1)·0,25 ab.
Jede Kachel besteht aus 5 × 5 Rasterzellen zu 0,05° (dasselbe Raster wie in
der Relaisleitung). "c" ist eine Bitmaske (hex): Bit r·5+s ist gesetzt, wenn
die Zelle in Zeile r (von Süden) und Spalte s (von Westen) ganz im Gebiet der
Auszüge liegt. Nur solche Zellen holt die Relaisleitung von hier, alles
andere weiter über Overpass.

Benötigt: osmium-tool, Python 3.9+, shapely.
Daten: © OpenStreetMap-Mitwirkende, Open Database License (ODbL) 1.0.
"""
import argparse
import hashlib
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

from shapely.geometry import Polygon, box as shp_box
from shapely.ops import unary_union

REGIONEN = ['europe/italy/nord-est', 'europe/austria']
GEOFABRIK = 'https://download.geofabrik.de/'
KACHEL = 0.25          # Grad
ZELLE = 0.05           # Grad, Raster der Relaisleitung
PRO = 5                # Zellen je Kachel und Richtung
EPS = 1e-6
ARTEN = {'fire_hydrant': 'hydrant', 'suction_point': 'suction', 'water_tank': 'tank', 'fire_water_pond': 'pond'}
NUR_PUNKTE = {'fire_hydrant'}  # wie die Overpass-Abfrage: Hydranten nur als Punkt
FORMAT = 'relaisleitung-hydranten-quelle'
# Straßen, deren Nummer ein Kilometerstein übernimmt (wenn er als Punkt auf ihr liegt)
KM_STRASSEN = ('motorway,motorway_link,trunk,trunk_link,primary,primary_link,secondary,secondary_link,'
               'tertiary,tertiary_link,unclassified,residential,service,track')
KM_RANG = {k: i for i, k in enumerate(['motorway', 'trunk', 'primary', 'secondary', 'tertiary'])}
LIZENZ = '© OpenStreetMap-Mitwirkende, Open Database License (ODbL) 1.0'
LIZENZ_KM = 'Kilometersteine in Südtirol: Autonome Provinz Bozen – Südtirol, Straßendienst (CC0)'
# Kilometersteine des Landes Südtirol (Open Data, CC0)
LANDES_WFS = 'https://geoservices1.civis.bz.it/geoserver/p_bz-TransportNetwork/ows'
LANDES_TYP = 'p_bz-TransportNetwork:Signs-Milestones'
LANDES_ARTEN = {1, 2}   # 1 Staats-/Landesstraße, 2 Autobahn (3 Gewässer, 4 Radroute nicht)


def log(*a):
    print(*a, flush=True)


def agent():
    repo = os.environ.get('GITHUB_REPOSITORY', 'lokal')
    return f'Relaisleitung-Hydranten/1.0 (+https://github.com/{repo})'


# ---------- Laden ----------

def laden(url, ziel, versuche=4):
    for n in range(1, versuche + 1):
        try:
            req = urllib.request.Request(url, headers={'User-Agent': agent()})
            with urllib.request.urlopen(req, timeout=120) as r, open(ziel, 'wb') as f:
                shutil.copyfileobj(r, f, 1 << 20)
            return
        except Exception as e:  # noqa: BLE001
            log(f'  Versuch {n}/{versuche} fehlgeschlagen: {e}')
            if n == versuche:
                raise
            time.sleep(20 * n)


def md5(pfad):
    h = hashlib.md5()
    with open(pfad, 'rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def region_holen(region, ordner):
    """PBF + Prüfsumme + Umriss (.poly) einer Geofabrik-Region laden."""
    name = region.rsplit('/', 1)[-1]
    pbf = os.path.join(ordner, f'{name}-latest.osm.pbf')
    poly = os.path.join(ordner, f'{name}.poly')
    for n in range(1, 4):
        log(f'Lade {region} …')
        laden(f'{GEOFABRIK}{region}-latest.osm.pbf.md5', pbf + '.md5')
        laden(f'{GEOFABRIK}{region}-latest.osm.pbf', pbf)
        soll = open(pbf + '.md5').read().split()[0].strip().lower()
        ist = md5(pbf)
        if soll == ist:
            break
        log(f'  Prüfsumme passt nicht ({ist} statt {soll}) – neu laden')
        if n == 3:
            raise SystemExit(f'{region}: Download beschädigt')
    laden(f'{GEOFABRIK}{region}.poly', poly)
    log(f'  {os.path.getsize(pbf) / 1e6:.0f} MB')
    return pbf, poly


# ---------- Umriss und Abdeckung ----------

def poly_lesen(pfad):
    """Geofabrik-.poly-Datei → shapely-Fläche (Abschnitte mit ! sind Löcher)."""
    zeilen = [z.strip() for z in open(pfad, encoding='utf-8')]
    aussen, loecher = [], []
    i = 1  # erste Zeile ist der Name
    while i < len(zeilen):
        kopf = zeilen[i]
        i += 1
        if kopf == 'END' or kopf == '':
            continue
        pkt = []
        while i < len(zeilen) and zeilen[i] != 'END':
            teile = zeilen[i].split()
            if len(teile) >= 2:
                pkt.append((float(teile[0]), float(teile[1])))  # Länge, Breite
            i += 1
        i += 1  # END des Abschnitts
        if len(pkt) >= 3:
            (loecher if kopf.startswith('!') else aussen).append(Polygon(pkt).buffer(0))
    flaeche = unary_union(aussen)
    if loecher:
        flaeche = flaeche.difference(unary_union(loecher))
    return flaeche


def abdeckung(flaeche):
    """{(i, j): maske} für alle Kacheln mit mindestens einer ganz abgedeckten Zelle."""
    w, s, e, n = flaeche.bounds
    ci0, ci1 = math.floor(s / ZELLE), math.ceil(n / ZELLE)
    cj0, cj1 = math.floor(w / ZELLE), math.ceil(e / ZELLE)
    from shapely.prepared import prep
    p = prep(flaeche)
    kacheln = {}
    for ci in range(ci0, ci1):
        for cj in range(cj0, cj1):
            zelle = shp_box(cj * ZELLE, ci * ZELLE, (cj + 1) * ZELLE, (ci + 1) * ZELLE)
            if not p.contains(zelle):
                continue
            ti, tj = ci // PRO, cj // PRO
            bit = (ci - ti * PRO) * PRO + (cj - tj * PRO)
            kacheln[(ti, tj)] = kacheln.get((ti, tj), 0) | (1 << bit)
    return kacheln


# ---------- Filtern und Einlesen ----------

def stand_lesen(pbf):
    """Datenstand aus dem Kopf der PBF-Datei (osmosis_replication_timestamp)."""
    try:
        j = json.loads(subprocess.run(['osmium', 'fileinfo', '-j', pbf], check=True,
                                      capture_output=True, text=True).stdout)
        opt = (j.get('header') or {}).get('option') or {}
        t = opt.get('osmosis_replication_timestamp') or opt.get('timestamp')
        if t:
            return t
    except Exception as e:  # noqa: BLE001
        log(f'  Stand nicht lesbar: {e}')
    return datetime.fromtimestamp(os.path.getmtime(pbf), timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def filtern(pbf, ziel):
    subprocess.run(['osmium', 'tags-filter', pbf,
                    'n/emergency=fire_hydrant',
                    'nwr/emergency=suction_point,water_tank,fire_water_pond',
                    '-o', ziel, '--overwrite', '--no-progress'], check=True)


def km_filtern(pbf, steine, strassen):
    """Kilometersteine und die Straßen (ohne Punkte), auf denen sie liegen könnten."""
    subprocess.run(['osmium', 'tags-filter', pbf, 'n/highway=milestone',
                    '-o', steine, '--overwrite', '--no-progress'], check=True)
    subprocess.run(['osmium', 'tags-filter', pbf, 'w/highway=' + KM_STRASSEN, '-R',
                    '-o', strassen, '--overwrite', '--no-progress'], check=True)


def km_zahl(text):
    """'23' / '22,5' / 'km 23.5' / '23 km' → 23.0 / 22.5 / 23.5; sonst None."""
    if not text:
        return None
    t = text.strip().lower().replace('km', '').replace(',', '.').strip()
    if '+' in t:  # 23+500
        a, _, b = t.partition('+')
        try:
            return round(float(a) + float(b) / 1000, 3)
        except ValueError:
            return None
    try:
        z = float(t)
    except ValueError:
        return None
    return round(z, 3) if 0 <= z < 10000 else None


def km_einlesen(steine_xml, strassen_xml, km):
    """Kilometersteine → km[id] = [Breite, Länge, Kilometer, Straße, id]."""
    neu = {}
    for _, el in ET.iterparse(steine_xml, events=('end',)):
        if el.tag != 'node':
            continue
        tags = {t.get('k'): t.get('v') for t in el.findall('tag')}
        if tags.get('highway') == 'milestone' and el.get('lat') is not None:
            d = km_zahl(tags.get('distance') or tags.get('pk') or tags.get('ele:km'))
            if d is not None:
                ref = tags.get('highway:ref') or tags.get('road') or tags.get('ref') or ''
                oid = int(el.get('id'))
                neu[oid] = [round(float(el.get('lat')), 7), round(float(el.get('lon')), 7), d, ref, oid]
        el.clear()
    if neu:
        bester = {}  # Stein-Id → (Rang, Nummer)
        for _, el in ET.iterparse(strassen_xml, events=('end',)):
            if el.tag != 'way':
                continue
            treffer = [int(nd.get('ref')) for nd in el.findall('nd') if int(nd.get('ref')) in neu]
            if treffer:
                tags = {t.get('k'): t.get('v') for t in el.findall('tag')}
                ref = (tags.get('ref') or '').split(';')[0].strip()
                if ref:
                    rang = KM_RANG.get(tags.get('highway', '').replace('_link', ''), 9)
                    for oid in treffer:
                        if oid not in bester or rang < bester[oid][0]:
                            bester[oid] = (rang, ref)
            el.clear()
        for oid, (_, ref) in bester.items():
            neu[oid][3] = ref
    for st in neu.values():
        st[3] = st[3].replace(' ', '')
    km.update(neu)
    return len(neu)


def utm32_wgs84(x, y):
    """ETRS89 / UTM 32N (EPSG:25832) → (Breite, Länge) in Grad; Genauigkeit weit unter 1 m."""
    a, f, k0 = 6378137.0, 1 / 298.257222101, 0.9996
    e2 = f * (2 - f)
    ep2 = e2 / (1 - e2)
    x -= 500000.0
    m = y / k0
    mu = m / (a * (1 - e2 / 4 - 3 * e2 ** 2 / 64 - 5 * e2 ** 3 / 256))
    e1 = (1 - math.sqrt(1 - e2)) / (1 + math.sqrt(1 - e2))
    p1 = (mu + (3 * e1 / 2 - 27 * e1 ** 3 / 32) * math.sin(2 * mu)
          + (21 * e1 ** 2 / 16 - 55 * e1 ** 4 / 32) * math.sin(4 * mu)
          + (151 * e1 ** 3 / 96) * math.sin(6 * mu) + (1097 * e1 ** 4 / 512) * math.sin(8 * mu))
    s1, c1 = math.sin(p1), math.cos(p1)
    t1 = math.tan(p1) ** 2
    n1 = a / math.sqrt(1 - e2 * s1 ** 2)
    r1 = a * (1 - e2) / (1 - e2 * s1 ** 2) ** 1.5
    cc = ep2 * c1 ** 2
    d = x / (n1 * k0)
    lat = p1 - (n1 * math.tan(p1) / r1) * (d ** 2 / 2 - (5 + 3 * t1 + 10 * cc - 4 * cc ** 2 - 9 * ep2) * d ** 4 / 24
                                           + (61 + 90 * t1 + 298 * cc + 45 * t1 ** 2 - 252 * ep2 - 3 * cc ** 2) * d ** 6 / 720)
    lon = (d - (1 + 2 * t1 + cc) * d ** 3 / 6 + (5 - 2 * cc + 28 * t1 - 3 * cc ** 2 + 8 * ep2 + 24 * t1 ** 2) * d ** 5 / 120) / c1
    return math.degrees(lat), 9.0 + math.degrees(lon)


def landes_km_laden(ziel_json):
    """Alle Kilometersteine vom WFS des Landes in eine Datei (seitenweise)."""
    basis = f'{LANDES_WFS}?service=WFS&version=2.0.0&request=GetFeature&typeNames={LANDES_TYP}&outputFormat=application/json'
    teil = ziel_json + '.teil'

    def holen(url):
        laden(url, teil, versuche=3)
        with open(teil, encoding='utf-8') as f:
            j = json.load(f)
        os.remove(teil)
        if not isinstance(j.get('features'), list):
            raise ValueError('keine features in der Antwort')
        return j['features']

    alle, start, seite = [], 0, 50000
    try:
        while True:   # seitenweise, sortiert nach ID
            feats = holen(f'{basis}&count={seite}&startIndex={start}&sortBy=ID')
            alle.extend(feats)
            log(f'  Land: {len(alle)} Steine geladen')
            if len(feats) < seite or start > 1000000:
                break
            start += seite
    except Exception as e:  # noqa: BLE001
        if alle:
            raise
        log(f'  Seitenweise Abfrage fehlgeschlagen ({e}) – alles auf einmal')
        alle = holen(basis)
        log(f'  Land: {len(alle)} Steine geladen')
    with open(ziel_json, 'w', encoding='utf-8') as f:
        json.dump({'features': alle}, f)


def landes_km_einlesen(pfad):
    """Landesdaten → Liste [Breite, Länge, Kilometer, Straße, Id, 'bz'] (nur Straßen und Autobahn)."""
    with open(pfad, encoding='utf-8') as f:
        feats = json.load(f).get('features') or []
    out, arten = [], {}
    for ft in feats:
        pr = ft.get('properties') or {}
        try:
            art = int(pr.get('TYPE_CODE'))
        except (TypeError, ValueError):
            art = None
        arten[art] = arten.get(art, 0) + 1
        if art not in LANDES_ARTEN:
            continue
        d = pr.get('POS_KM')
        if d is None and pr.get('POS_M') is not None:
            d = float(pr['POS_M']) / 1000
        try:
            d = round(float(d), 3)
        except (TypeError, ValueError):
            continue
        if not 0 <= d < 10000:
            continue
        lat = lon = None
        try:   # amtliche Koordinaten (UTM 32N, cm-genau) – die Geometrie des Dienstes ist gerundet
            x, y = float(pr['COORD_X']), float(pr['COORD_Y'])
            if 200000 < x < 900000 and 4000000 < y < 6000000:
                lat, lon = utm32_wgs84(x, y)
        except (KeyError, TypeError, ValueError):
            pass
        if lat is None:
            c = ((ft.get('geometry') or {}).get('coordinates') or [None, None])
            try:
                a, b = float(c[0]), float(c[1])
            except (TypeError, ValueError, IndexError):
                continue
            if 40 < a < 50 and 5 < b < 20:
                a, b = b, a   # Achsen vertauscht
            if not (5 < a < 20 and 40 < b < 50):
                continue
            lon, lat = a, b
        ref = str(pr.get('ROAD_CODE_DE') or pr.get('ROAD_CODE_IT') or '').replace('.', '').replace(' ', '')
        oid = pr.get('ID', ft.get('id'))
        out.append([round(lat, 7), round(lon, 7), d, ref, f'bz{oid}', 'bz'])
    log(f'  Land: Arten {dict(sorted(arten.items(), key=lambda kv: str(kv[0])))}, davon {len(out)} Straßen-/Autobahnsteine')
    return out


def km_zusammen(km_osm, landes):
    """Landessteine haben Vorrang: OSM-Steine mit gleichem Kilometer im Umkreis von 300 m fallen weg."""
    if not landes:
        return [st + ['osm'] for st in km_osm.values()]
    raster = {}
    for st in landes:
        raster.setdefault((round(st[0] / 0.01), round(st[1] / 0.01)), []).append(st)
    out, weg = list(landes), 0
    for st in km_osm.values():
        gi, gj = round(st[0] / 0.01), round(st[1] / 0.01)
        doppelt = False
        for di in (-1, 0, 1):
            for dj in (-1, 0, 1):
                for l in raster.get((gi + di, gj + dj), ()):
                    if abs(l[2] - st[2]) < 0.001:
                        dy = (l[0] - st[0]) * 111320
                        dx = (l[1] - st[1]) * 111320 * math.cos(math.radians(st[0]))
                        if dx * dx + dy * dy < 300 ** 2:
                            doppelt = True
        if doppelt:
            weg += 1
        else:
            out.append(st + ['osm'])
    log(f'Kilometersteine: {len(landes)} vom Land, {len(km_osm) - weg} aus OpenStreetMap ({weg} doppelte OSM-Steine weggelassen)')
    return out


def einlesen(osm_xml, elemente):
    """Gefilterte OSM-XML-Datei → Einträge im Overpass-Format (mit center für Flächen)."""
    knoten, wege, rel = {}, {}, []
    for _, el in ET.iterparse(osm_xml, events=('end',)):
        if el.tag not in ('node', 'way', 'relation'):
            continue
        tags = {t.get('k'): t.get('v') for t in el.findall('tag')}
        oid = int(el.get('id'))
        if el.tag == 'node':
            if el.get('lat') is not None:
                knoten[oid] = (float(el.get('lat')), float(el.get('lon')), tags)
        elif el.tag == 'way':
            wege[oid] = ([int(nd.get('ref')) for nd in el.findall('nd')], tags)
        else:
            rel.append((oid, [(m.get('type'), int(m.get('ref'))) for m in el.findall('member')], tags))
        el.clear()

    def passt(typ, tags):
        art = tags.get('emergency')
        return art in ARTEN and (typ == 'node' or art not in NUR_PUNKTE)

    def mitte(punkte):
        punkte = [p for p in punkte if p]
        if not punkte:
            return None
        la = [p[0] for p in punkte]
        lo = [p[1] for p in punkte]
        return (min(la) + max(la)) / 2, (min(lo) + max(lo)) / 2

    for oid, (lat, lon, tags) in knoten.items():
        if passt('node', tags):
            elemente[('node', oid)] = {'type': 'node', 'id': oid, 'lat': round(lat, 7), 'lon': round(lon, 7), 'tags': tags}
    for oid, (refs, tags) in wege.items():
        if passt('way', tags):
            m = mitte([knoten.get(r) for r in refs])
            if m:
                elemente[('way', oid)] = {'type': 'way', 'id': oid, 'center': {'lat': round(m[0], 7), 'lon': round(m[1], 7)}, 'tags': tags}
    for oid, mitglieder, tags in rel:
        if not passt('relation', tags):
            continue
        pkt = []
        for typ, ref in mitglieder:
            if typ == 'node':
                pkt.append(knoten.get(ref))
            elif typ == 'way' and ref in wege:
                pkt.extend(knoten.get(r) for r in wege[ref][0])
        m = mitte(pkt)
        if m:
            elemente[('relation', oid)] = {'type': 'relation', 'id': oid, 'center': {'lat': round(m[0], 7), 'lon': round(m[1], 7)}, 'tags': tags}


# ---------- Schreiben ----------

def lage(el):
    return (el['lat'], el['lon']) if el['type'] == 'node' else (el['center']['lat'], el['center']['lon'])


def zahl(n):
    return f'{n:,}'.replace(',', '.')


def html_seite(idx):
    arten = idx['arten']
    zeilen = ''.join(f'<tr><td>{k}</td><td>{zahl(v)}</td></tr>' for k, v in [
        ('Hydranten', arten.get('hydrant', 0)), ('Saugstellen', arten.get('suction', 0)),
        ('Löschwasserbehälter', arten.get('tank', 0)), ('Löschteiche', arten.get('pond', 0)),
        ('Kilometersteine', sum((idx.get('km') or {}).values())),
        ('davon vom Land Südtirol', (idx.get('km_quellen') or {}).get('bz', 0))])
    stand = ', '.join(f'{r}: {t[:10]}' for r, t in idx['regionen'].items())
    erzeugt = idx['erzeugt'][:16].replace('T', ' ')
    return f'''<!doctype html>
<html lang="de"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Hydranten-Quelle</title>
<style>body{{font:16px/1.5 system-ui,sans-serif;max-width:40rem;margin:2rem auto;padding:0 1rem;color:#1b2430}}
h1{{font-size:1.4rem}}table{{border-collapse:collapse}}td{{padding:.2rem 1rem .2rem 0}}td+td{{text-align:right}}
small{{color:#5b6573}}</style></head><body>
<h1>Hydranten-Quelle für die Relaisleitung</h1>
<p>Stand der Daten: <b>{idx["stand"][:10]}</b> ({stand})<br>Erzeugt: {erzeugt} UTC</p>
<table>{zeilen}</table>
<p>{zahl(idx["anzahl"])} Einträge in {zahl(len(idx["kacheln"]))} Kacheln.</p>
<p><small>Daten: {LIZENZ}. {LIZENZ_KM}. Gefiltert aus den Auszügen von Geofabrik. Die Relaisleitung lädt <code>index.json</code> und die Kacheln unter <code>k/</code>, das Whiteboard zusätzlich die Kilometersteine unter <code>km/</code>.</small></p>
</body></html>
'''


def schreiben(ziel, elemente, abdeck, regionen, km=None):
    if os.path.isdir(ziel):
        shutil.rmtree(ziel)
    os.makedirs(os.path.join(ziel, 'k'))
    os.makedirs(os.path.join(ziel, 'km'))
    km_gruppen, km_quellen = {}, {}
    for st in (km or []):
        km_quellen[st[5]] = km_quellen.get(st[5], 0) + 1
        km_gruppen.setdefault((math.floor(st[0] / KACHEL), math.floor(st[1] / KACHEL)), []).append(st)
    km_index = {}
    gruppen = {}
    for el in elemente.values():
        la, lo = lage(el)
        gruppen.setdefault((math.floor(la / KACHEL), math.floor(lo / KACHEL)), []).append(el)
    kacheln = {}
    arten = {}
    for (i, j), maske in sorted(abdeck.items()):
        els = sorted(gruppen.get((i, j), []), key=lambda e: (e['type'], e['id']))
        eintrag = {'n': len(els), 'c': format(maske, 'x')}
        if els:
            with open(os.path.join(ziel, 'k', f'{i}_{j}.json'), 'w', encoding='utf-8') as f:
                json.dump({'elements': els}, f, ensure_ascii=False, separators=(',', ':'))
        kacheln[f'{i}_{j}'] = eintrag
        steine = sorted(km_gruppen.get((i, j), []), key=lambda st: (st[3], st[2], str(st[4])))
        if steine:
            with open(os.path.join(ziel, 'km', f'{i}_{j}.json'), 'w', encoding='utf-8') as f:
                json.dump({'km': [[st[0], st[1], int(st[2]) if st[2] == int(st[2]) else st[2], st[3], st[4], st[5]]
                                  for st in steine]}, f, ensure_ascii=False, separators=(',', ':'))
            km_index[f'{i}_{j}'] = len(steine)
        for e in els:
            a = ARTEN[e['tags']['emergency']]
            arten[a] = arten.get(a, 0) + 1
    stand = min(regionen.values())
    idx = {
        'format': FORMAT, 'v': 1,
        'stand': stand,
        'erzeugt': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
        'regionen': regionen,
        'kachel': KACHEL, 'zelle': ZELLE,
        'anzahl': sum(k['n'] for k in kacheln.values()),
        'arten': arten,
        'lizenz': LIZENZ,
        'kacheln': kacheln,
        'km': km_index,
        'km_quellen': km_quellen,
        'lizenz_km': LIZENZ_KM,
    }
    with open(os.path.join(ziel, 'index.json'), 'w', encoding='utf-8') as f:
        json.dump(idx, f, ensure_ascii=False, separators=(',', ':'))
    with open(os.path.join(ziel, 'index.html'), 'w', encoding='utf-8') as f:
        f.write(html_seite(idx))
    open(os.path.join(ziel, '.nojekyll'), 'w').close()
    return idx


def vergleichen(idx, vorher_pfad, min_anteil):
    """Bricht ab, wenn deutlich weniger Einträge als beim letzten Lauf herauskommen."""
    if not vorher_pfad or not os.path.isfile(vorher_pfad) or os.path.getsize(vorher_pfad) == 0:
        log('Kein früherer Stand zum Vergleich.')
        return
    try:
        alt = json.load(open(vorher_pfad, encoding='utf-8'))
    except Exception as e:  # noqa: BLE001
        log(f'Früherer Stand nicht lesbar ({e}) – kein Vergleich.')
        return
    n_alt, n_neu = alt.get('anzahl', 0), idx['anzahl']
    log(f'Vorher {n_alt} Einträge, jetzt {n_neu}.')
    if n_alt and n_neu < n_alt * min_anteil:
        raise SystemExit(f'Abbruch: nur {n_neu} statt bisher {n_alt} Einträge – Auszug unvollständig? '
                         'Nichts veröffentlicht, der alte Stand bleibt.')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--ziel', default='site', help='Ausgabeordner für GitHub Pages')
    ap.add_argument('--regionen', nargs='+', default=REGIONEN, help='Geofabrik-Regionen, z. B. europe/austria')
    ap.add_argument('--lokal', help='Ordner mit bereits geladenen <name>-latest.osm.pbf und <name>.poly (zum Testen)')
    ap.add_argument('--vorher', help='index.json des letzten Laufs zum Vergleich')
    ap.add_argument('--min-anteil', type=float, default=0.7, help='Abbruch unter diesem Anteil des letzten Stands')
    ap.add_argument('--landes-datei', help='Kilometersteine des Landes aus dieser GeoJSON-Datei statt vom WFS (zum Testen)')
    ap.add_argument('--ohne-land', action='store_true', help='Kilometersteine des Landes weglassen')
    a = ap.parse_args()

    arbeit = tempfile.mkdtemp(prefix='hydranten-')
    elemente, flaechen, regionen, km = {}, [], {}, {}
    for region in a.regionen:
        name = region.rsplit('/', 1)[-1]
        if a.lokal:
            pbf = os.path.join(a.lokal, f'{name}-latest.osm.pbf')
            poly = os.path.join(a.lokal, f'{name}.poly')
        else:
            pbf, poly = region_holen(region, arbeit)
        regionen[region] = stand_lesen(pbf)
        gefiltert = os.path.join(arbeit, f'{name}.osm')
        filtern(pbf, gefiltert)
        vorher = len(elemente)
        einlesen(gefiltert, elemente)
        steine, strassen = os.path.join(arbeit, f'{name}-km.osm'), os.path.join(arbeit, f'{name}-str.osm')
        km_filtern(pbf, steine, strassen)
        log(f'{region}: {km_einlesen(steine, strassen, km)} Kilometersteine')
        os.remove(strassen)
        flaechen.append(poly_lesen(poly))
        log(f'{region}: Stand {regionen[region]}, {len(elemente) - vorher} neue Einträge')
        if not a.lokal:
            os.remove(pbf)
    landes = []
    if not a.ohne_land:
        try:
            pfad = a.landes_datei
            if not pfad:
                log('Lade Kilometersteine des Landes Südtirol …')
                pfad = os.path.join(arbeit, 'land-km.json')
                landes_km_laden(pfad)
            landes = landes_km_einlesen(pfad)
        except Exception as e:  # noqa: BLE001 – ohne Landesdaten weiter, nur OSM
            log(f'WARNUNG: Kilometersteine des Landes nicht geladen ({e}) – nur OpenStreetMap.')
    km_liste = km_zusammen(km, landes)
    abdeck = abdeckung(unary_union(flaechen))
    idx = schreiben(a.ziel, elemente, abdeck, regionen, km_liste)
    if idx['anzahl'] == 0:
        raise SystemExit('Abbruch: keine Einträge gefunden.')
    log(f'{idx["anzahl"]} Einträge in {len(idx["kacheln"])} Kacheln, Arten: {idx["arten"]}, '
        f'Kilometersteine: {sum(idx["km"].values())}')
    ausserhalb = len(elemente) - idx['anzahl']
    if ausserhalb:
        log(f'({ausserhalb} Einträge liegen in Kacheln ohne ganz abgedeckte Zelle und werden nicht veröffentlicht)')
    vergleichen(idx, a.vorher, a.min_anteil)
    shutil.rmtree(arbeit, ignore_errors=True)


if __name__ == '__main__':
    main()
