#!/usr/bin/env python3
"""Hydranten-Quelle für die Relaisleitung

Lädt OpenStreetMap-Auszüge von Geofabrik, filtert Hydranten, Saugstellen,
Löschwasserbehälter und Löschteiche heraus und schreibt sie als Kacheln
für GitHub Pages:

  index.json        Stand, Anzahl, Kachelliste mit Abdeckung je Rasterzelle
  k/<i>_<j>.json    Einträge einer Kachel (0,25° × 0,25°) im Overpass-Format
  index.html        kurze Übersicht zum Nachschauen im Browser

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
LIZENZ = '© OpenStreetMap-Mitwirkende, Open Database License (ODbL) 1.0'


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
        ('Löschwasserbehälter', arten.get('tank', 0)), ('Löschteiche', arten.get('pond', 0))])
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
<p><small>Daten: {LIZENZ}. Gefiltert aus den Auszügen von Geofabrik. Die Relaisleitung lädt <code>index.json</code> und die Kacheln unter <code>k/</code>.</small></p>
</body></html>
'''


def schreiben(ziel, elemente, abdeck, regionen):
    if os.path.isdir(ziel):
        shutil.rmtree(ziel)
    os.makedirs(os.path.join(ziel, 'k'))
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
    a = ap.parse_args()

    arbeit = tempfile.mkdtemp(prefix='hydranten-')
    elemente, flaechen, regionen = {}, [], {}
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
        flaechen.append(poly_lesen(poly))
        log(f'{region}: Stand {regionen[region]}, {len(elemente) - vorher} neue Einträge')
        if not a.lokal:
            os.remove(pbf)
    abdeck = abdeckung(unary_union(flaechen))
    idx = schreiben(a.ziel, elemente, abdeck, regionen)
    if idx['anzahl'] == 0:
        raise SystemExit('Abbruch: keine Einträge gefunden.')
    log(f'{idx["anzahl"]} Einträge in {len(idx["kacheln"])} Kacheln, Arten: {idx["arten"]}')
    ausserhalb = len(elemente) - idx['anzahl']
    if ausserhalb:
        log(f'({ausserhalb} Einträge liegen in Kacheln ohne ganz abgedeckte Zelle und werden nicht veröffentlicht)')
    vergleichen(idx, a.vorher, a.min_anteil)
    shutil.rmtree(arbeit, ignore_errors=True)


if __name__ == '__main__':
    main()
