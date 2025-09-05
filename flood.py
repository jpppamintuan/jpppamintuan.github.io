# -*- coding: utf-8 -*-
"""
Created on Thu Aug 21 13:21:21 2025

@author: Paolo
"""

# 1. Imports and Global Configuration
# -----------------------------------------------------------------------------
import pandas as pd
import geopandas as gpd
import folium
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from bs4 import BeautifulSoup
import re
from urllib.parse import urljoin
import sys
import os
import folium.features
from folium.features import FeatureGroup
from folium.features import Element
from shapely.geometry import Point, Polygon
from shapely.validation import make_valid
from shapely.ops import polylabel
from datetime import datetime, timedelta
import math
import xml.etree.ElementTree as ET
import traceback
import time
import pytz
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC

# Combine Global Variables
island_groups = {
    'Abra': 'Luzon',
    'Agno': 'Luzon',
    'Apayao-Abulug': 'Luzon',
    'Bicol': 'Luzon',
    'Cagayan': 'Luzon',
    'NCR/Pasig Marikina Laguna de Bay': 'Luzon',
    'Pampanga': 'Luzon',
    'Ambuklao-Binga-San Roque Sub-basin': 'Luzon',
    'Angat Sub-basin': 'Luzon',
    'Magat Sub-basin': 'Luzon',
    'Pantabangan Sub-basin': 'Luzon',
    'Ilog-Hilabangan': 'Visayas',
    'Jalaur': 'Visayas',
    'Panay': 'Visayas',
    'Agus': 'Mindanao',
    'Agusan': 'Mindanao',
    'Buayan-Malungon': 'Mindanao',
    'Cagayan De Oro': 'Mindanao',
    'Davao': 'Mindanao',
    'Mindanao': 'Mindanao',
    'Tagoloan': 'Mindanao',
    'Tagum-Libuganon': 'Mindanao',
}

island_group_order = ['Luzon', 'Visayas', 'Mindanao', 'Others']

region_order_map = {
    "NCR (National Capital Region)": 0,
    "Region 1 (Ilocos Region)": 1,
    "CAR (Cordillera Administrative Region)": 2,
    "Region 2 (Cagayan Valley)": 3,
    "Region 3 (Central Luzon)": 4,
    "Region 4-A (CALABARZON)": 5,
    "Region 4-B (MIMAROPA)": 6,
    "Region 5 (Bicol Region)": 7,
    "Region 6 (Western Visayas)": 8,
    "Region 7 (Central Visayas)": 9,
    "Region 8 (Eastern Visayas)": 10,
    "Region 9 (Zamboanga Peninsula)": 11,
    "Region 10 (Northern Mindanao)": 12,
    "Region 11 (Davao Region)": 13,
    "Region 12 (SOCCSKSARGEN)": 14,
    "Region 13 (Caraga)": 15,
    "BARMM (Bangsamoro Autonomous Region in Muslim Mindanao)": 16,
    "N/A Region": 999
}

# Combine Other Global Variables
provinces_by_gfa_type_for_summary = {}
gfa_category_order = [
    "Flood Warning",
    "Flood Alert",
    "Flood Monitoring",
    "Final Advisory"
]

# 2. Helper Functions
# -----------------------------------------------------------------------------
def format_issued_time(sent_str):
    try:
        sent_dt = datetime.fromisoformat(sent_str.replace('Z', '+00:00'))
    except ValueError:
        return f"N/A, {datetime.now().strftime('%d %B %Y')}", "", False

    morning_start = sent_dt.replace(hour=4, minute=0, second=0, microsecond=0)
    morning_end = sent_dt.replace(hour=7, minute=0, second=0, microsecond=0)
    evening_start = sent_dt.replace(hour=16, minute=0, second=0, microsecond=0)
    evening_end = sent_dt.replace(hour=19, minute=0, second=0, microsecond=0)

    display_time_str = ""
    validity_info = ""
    is_standard_time = False

    if morning_start <= sent_dt <= morning_end:
        display_time_str = "6:00 am"
        validity_info = "Valid until the next issuance at 6:00 pm today"
        is_standard_time = True
    elif evening_start <= sent_dt <= evening_end:
        display_time_str = "6:00 pm"
        validity_info = "Valid until the next issuance at 6:00 am tomorrow"
        is_standard_time = True
    else:
        time_to_round = sent_dt.replace(second=0, microsecond=0)
        total_minutes_since_midnight = time_to_round.hour * 60 + time_to_round.minute

        # Round up to the nearest 30-minute interval
        rounded_total_minutes = math.ceil(total_minutes_since_midnight / 30) * 30

        start_of_day_sent = sent_dt.replace(hour=0, minute=0, second=0, microsecond=0)
        rounded_dt_for_display = start_of_day_sent + timedelta(minutes=rounded_total_minutes)
        display_time_str = rounded_dt_for_display.strftime("%I:%M %p").lower().replace('am', 'am').replace('pm', 'pm')

        if sent_dt.hour < 6:
            validity_info = "Valid until the next issuance at 6:00 am tomorrow"
        elif sent_dt.hour < 18:
            validity_info = "Valid until the next issuance at 6:00 pm today"
        else:
            validity_info = "Valid until the next issuance at 6:00 am tomorrow"
    
    date_part = sent_dt.strftime("%d %B %Y")
    
    return f"{display_time_str}, {date_part}", validity_info, is_standard_time

def get_styled_province_function(province_info_dict):
    def styled_province_function(feature):
        province_name_from_geojson = feature['properties'].get('adm2_en')

        if isinstance(province_name_from_geojson, str):
            cleaned_province_name_geojson_lower = province_name_from_geojson.replace('Province of ', '').strip().lower()
        else:
            cleaned_province_name_geojson_lower = None

        info = province_info_dict.get(cleaned_province_name_geojson_lower, {'color': 'white', 'severity_level': 0})
        fill_color = info['color']
        fill_opacity = 0.9 if fill_color != 'white' else 0
        weight = 0.6 if fill_color != 'white' else 0.1

        return {
            'fillColor': fill_color,
            'color': 'black',
            'weight': weight,
            'fillOpacity': fill_opacity,
        }
    return styled_province_function

def process_instruction_text(instruction_text):
    if not isinstance(instruction_text, str):
        return instruction_text
    
    modified_text_step1 = instruction_text

    instruction_lower = instruction_text.lower()
    if "flashfloods" in instruction_lower and "landslides" not in instruction_lower:
        modified_text_step1 = re.sub(
            r'flashfloods',
            r'flashfloods and landslides',
            instruction_text,
            count=1,
            flags=re.IGNORECASE
        )

    modified_text_step2 = modified_text_step1.strip()
    modified_text_step2 = modified_text_step2.rstrip('.')
    modified_text_step2 += '.'

    return modified_text_step2

def generate_tooltip_html(feature, province_info_dict):
    province_name_from_geojson = feature['properties'].get('adm2_en')
    if isinstance(province_name_from_geojson, str):
        cleaned_province_name_geojson_lower = province_name_from_geojson.replace('Province of ', '').strip().lower()
    else:
        cleaned_province_name_geojson_lower = None

    info = province_info_dict.get(cleaned_province_name_geojson_lower, {
        'color': 'white',
        'severity_level': 0,
        'event': 'No Advisory',
        'identifier': 'N/A',
        'region': 'N/A',
        'sent': 'N/A',
        'instruction': 'No specific instructions.',
        'rivers_info': 'N/A',
        'present_weather': 'N/A',
        'rainfall_forecast': 'N/A'
    })

    original_event = info['event']
    display_event_text = original_event

    if 'moderate' in original_event.lower():
        display_event_text = 'Flood Monitoring'
    elif 'severe' in original_event.lower():
        display_event_text = 'Flood Alert'
    elif 'extreme' in original_event.lower():
        display_event_text = 'Flood Warning'
    elif 'final' in original_event.lower():
        display_event_text = 'Final'

    background_color_code = info['color']
    text_color_code = 'black'
    if background_color_code in ['#B22B42', '#E6793B', '#777777']:
        text_color_code = 'white'

    event_status_style = f"background-color: {background_color_code}; color: {text_color_code}; padding: 2px 5px; border-radius: 3px; font-weight: bold;"

    html_content = ""

    if info['region'] != 'N/A':
        html_content += f"""
    <strong>Region:</strong> {info['region']}<br>
        """

    html_content += f"""
    <strong>Province:</strong> {province_name_from_geojson or 'N/A'}<br>
    <strong>General Flood Advisory:</strong> <span style="{event_status_style}">{display_event_text}</span>
    """

    if display_event_text == 'Final':
        html_content += f"""
            <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max-width: 100%;"><br>Flood is no longer likely unless significant rain occurs.</div>
            """

    if info['severity_level'] > 0:
        instruction_text = info.get('instruction', 'No specific instructions.')
        if not instruction_text.strip():
            instruction_text = 'No specific instructions.'

        instruction_text = instruction_text.replace('**', '')
        modified_instruction_text = re.sub(r'(concerned)(?!\w)', r'\1 are', instruction_text, flags=re.IGNORECASE, count=1)
        modified_instruction_text = re.sub(r'(near)\s+the\s+(mountain slopes)', r'\1 \2', modified_instruction_text, flags=re.IGNORECASE)
        modified_instruction_text = re.sub(r'(in)\s+the\s+(low lying areas)', r'\1 \2', modified_instruction_text, flags=re.IGNORECASE)
        final_instruction_text = modified_instruction_text

        phrases_to_underline = [
            r"near mountain slopes",
            r"in low lying areas"
        ]
        for phrase_pattern in phrases_to_underline:
            final_instruction_text = re.sub(
                r'(' + phrase_pattern + r')',
                r'<u>\1</u>',
                final_instruction_text,
                flags=re.IGNORECASE
            )

        idx_to = final_instruction_text.lower().find("to")

        if idx_to != -1:
            part_before_to = final_instruction_text[:idx_to]

            len_to = len("to")

            part_to_format = final_instruction_text[idx_to + len_to:]

            trailing_period = ''
            if part_to_format.endswith('.'):
                trailing_period = '.'
                part_to_format = part_to_format[:-1]

            instruction_style = "font-weight: bold; text-decoration: underline;"

            final_instruction_text = (
                part_before_to +
                "to " +
                f"<span style='{instruction_style}'>{part_to_format}</span>" +
                trailing_period
            )

        instruction_html_content = f'<div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max-width: 100%;">{final_instruction_text}</div>'

        issued_date_time, validity_period, is_standard_time = format_issued_time(info['sent'])

        html_content += f"""<br>
    <strong>Issued at:</strong> {issued_date_time}<br>
    {validity_period}<br>
        """

        present_weather = info.get('present_weather')
        if present_weather and present_weather != 'N/A':
            html_content += f"""<br>
    <strong>Present weather:</strong> <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max_width: 100%;">{present_weather}</div>
            """

        rainfall_forecast = info.get('rainfall_forecast')
        if rainfall_forecast and rainfall_forecast != 'N/A':
            html_content += f"""
    <strong>Forecast 12-hour rainfall:</strong> <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max_width: 100%;">{rainfall_forecast}</div>
            """

        rivers_info = info.get('rivers_info')
        if rivers_info and rivers_info != 'N/A':
            html_content += f"""
    <strong>Watercourses likely to be affected:</strong> <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max_width: 100%;">{rivers_info}</div>
            """

        html_content += f"""<br>
    <strong>Instruction:</strong> {instruction_html_content}
        """
    return html_content
    
def get_severity_color(severity_string):
    if severity_string:
        severity_string_lower = severity_string.lower()
        if 'extreme' in severity_string_lower:
            return '#B22B42'
        elif 'severe' in severity_string_lower:
            return '#E6793B'
        elif 'moderate' in severity_string_lower:
            return '#F3C218'
        elif 'minor' in severity_string_lower or 'unknown' in severity_string_lower or 'none' in severity_string_lower:
            return '#777777'
    return 'white'

def get_severity_level(severity_string):
    if severity_string:
        severity_string_lower = severity_string.lower() 
        if 'extreme' in severity_string_lower:
            return 3
        elif 'severe' in severity_string_lower:
            return 2
        elif 'moderate' in severity_string_lower:
            return 1
    return 0

provinces_by_gfa_type_for_summary = {}

gfa_category_order = [
    "Flood Warning",
    "Flood Alert",
    "Flood Monitoring",
    "Final Advisory"
]

def format_gfa_provinces(provinces_by_gfa_type, event_details, issued_date_time_part, validity_info_part):
    color_map = {
        "Flood Warning": {"background": "#B22B42", "text": "#FFFFFF"},
        "Flood Alert": {"background": "#E6793B", "text": "#FFFFFF"},
        "Flood Monitoring": {"background": "#F3C218", "text": "#000000"},
        "Final Advisory": {"background": "#777777", "text": "#FFFFFF"},
        # "No Advisory": {"background": "#DDDDDD", "text": "#333333"}
    }

    formatted_html = """
    """
    if not provinces_by_gfa_type:
         formatted_html += f"""
        <div style="font-size: 14px; margin-top: 32px; text-align: center; color: #333;">Currently, there are no active General Flood Advisories.</div>
        """
    else:
        for gfa_type in gfa_category_order:
            if gfa_type in provinces_by_gfa_type:
                provinces = provinces_by_gfa_type[gfa_type]
                colors = color_map.get(gfa_type, {"background": "#FFFFFF", "text": "#333333"})
                details = event_details.get(gfa_type, {'text': '', 'icon': ''})
                
                icon_html = f'<img src="{details["icon"]}" style="width: 36px; height: 36px; margin-right: 2px; flex-shrink: 0;">' if details['icon'] else ''

                formatted_html += f"""
                <div style="
                    font-size: 14px;
                    display: flex;
                    align-items: center;
                    width: 100%;
                    text-align: left;
                    margin-top: 8px;
                    padding: 4px 8px 5px 4px;
                    border-radius: 3px;
                    background-color: {colors['background']};
                    color: {colors['text']};
                    font-weight: bold;
                ">
                    {icon_html}
                    <div style="flex-grow: 1;">
                        {gfa_type}
                        <div style="font-size: 12px; font-weight: normal; line-height: 1.2;">{details['text']}</div>
                    </div>
                </div>
                <ul style='margin: 0; margin-top: 4px; padding-left: 20px; list-style-type: disc; list-style-position: outside; column-count: 3; column-gap: 16px; line-height: 1.3; break-inside: avoid;'>
                """
                for province in provinces:
                    formatted_html += f"<li style='font-size: 12px; margin-bottom: 2px; color: #333;'>{province}</li>"
                formatted_html += "</ul>"
    return formatted_html

def fetch_page(url, session):
    """Fetches a webpage and returns its BeautifulSoup object."""
    try:
        response = session.get(url, timeout=10)
        response.raise_for_status()
        return BeautifulSoup(response.content, "html.parser")
    except requests.RequestException as e:
        print(f"⚠️ Failed to fetch {url}: {e}", file=sys.stderr)
        return None

def format_issued_at(text):
    if text == 'N/A':
        return text
    text = text.title()
    text = text.replace('Am', 'am').replace('Pm', 'pm')
    return text

def to_sentence_case(text):
    if text == 'N/A':
        return text
    return text.capitalize()

def format_water_level(text):
    if text == 'N/A':
        return text
    text = to_sentence_case(text)
    match = re.search(r'(?<=expected to )([\s\S]+?)(?= during)', text, re.IGNORECASE)
    if match:
        phrase_to_format = match.group(1)
        formatted_phrase = f"<u><b>{phrase_to_format.upper()}</b></u>"
        text = text.replace(phrase_to_format, formatted_phrase)
    return text

def format_status_badge(status):
    if status == 'Non-Flood Watch':
        return f'<span style="background-color: #009BFF; padding: 2px 5px; border-radius: 3px; color: white; font-weight: bold;">Non-Flood Watch</span>'
    elif status == 'Flood Watch':
        return f'<span style="background-color: #C0392B; padding: 2px 5px; border-radius: 3px; color: white; font-weight: bold;">{status}</span>'
    else:
        return status

def generate_grouped_list_html(basins_df, color_code, font_size):
    if basins_df.empty:
        return ""
    grouped_html = ""
    for group in island_group_order:
        group_df = basins_df[basins_df['Island Group'] == group]
        if not group_df.empty:
            list_items = ""
            for _, basin in group_df.iterrows():
                italic_style = "font-style: italic;" if basin['is_subbasin'] else ""
                name = basin['River Basin']
                link = basin['Link']
                if link:
                    list_items += f'<li style="{italic_style}"><a href="{link}" target="_blank" style="color: {color_code}">{name}</a></li>'
                else:
                    list_items += f'<li style="{italic_style}color: {color_code}">{name}</li>'
            grouped_html += f"""
                <div style="font-size: {font_size}; font-weight: bold; margin-top: 5px;">{group}</div>
                <ul class="basin-list" style="padding-left: 20px; margin: 0 0 7px 0; font-size: {font_size}; column-count: 2;">
                    {list_items}
                </ul>
            """
    return grouped_html

# 3. Data Extraction Functions
# -----------------------------------------------------------------------------
def extract_gfa_identifiers(target_date_str: str, am_pm_str: str):
    target_url = "https://publicalert.pagasa.dost.gov.ph/output/gfa/?C=M;O=D"
    matching_identifiers = []

    try:
        target_date_obj = datetime.strptime(target_date_str, '%Y-%m-%d').date()
    except ValueError:
        print(f"Error: Invalid date format '{target_date_str}'. Please use YYYY-MM-DD.")
        return []

    start_hour = 0
    end_hour = 0

    if am_pm_str.lower() == 'am':
        start_hour = 0
        end_hour = 11
        print(f"Searching for advisories on {target_date_str} (am: 00:00 - 11:59)...")
    elif am_pm_str.lower() == 'pm':
        start_hour = 12
        end_hour = 23
        print(f"Searching for advisories on {target_date_str} (pm: 12:00 - 23:59)...")
    else:
        print(f"Error: Invalid AM/PM input '{am_pm_str}'. Please use 'am' or 'pm'.")
        return []

    print(f"Attempting to extract GFA identifiers from: {target_url}...")
    try:
        retries = Retry(total=3, backoff_factor=1, status_forcelist=[500, 502, 503, 504])
        adapter = HTTPAdapter(max_retries=retries)
        session = requests.Session()
        session.mount("https://", adapter)
        session.mount("http://", adapter)

        response = session.get(target_url, timeout=10)
        response.raise_for_status()

        soup = BeautifulSoup(response.content, 'html.parser')
        
        cap_links = soup.find_all('a', href=re.compile(r'^(?!.*\.\./).*(\.cap)$'))

        for link in cap_links:
            href = link.get('href')
            identifier = href.replace('.cap', '')

            if not re.fullmatch(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}', identifier):
                continue

            parent_td = link.find_parent('td')
            if parent_td:
                parent_tr = parent_td.find_parent('tr')
                if parent_tr:
                    tds = parent_tr.find_all('td')
                    if len(tds) > 2:
                        time_str_raw = tds[2].get_text(strip=True)
                        try:
                            modification_time = datetime.strptime(time_str_raw, '%d-%b-%Y %H:%M')
                            if modification_time.date() < target_date_obj:
                                print(f"Encountered an advisory older than {target_date_obj}. Stopping search early.")
                                break

                            if (modification_time.date() == target_date_obj and
                                start_hour <= modification_time.hour <= end_hour):
                                matching_identifiers.append(identifier)

                        except ValueError:
                            print(f"Warning: Could not parse date/time '{time_str_raw}' for identifier {identifier}. Skipping.")
                            continue
    
    except requests.exceptions.RequestException as e:
        print(f"Error fetching URL ({target_url}): {e}")
        return []
    except Exception as e:
        print(f"An error occurred during HTML parsing ({target_url}): {e}")
        traceback.print_exc()
        return []

    if not matching_identifiers:
        print(f"No CAP identifiers found for {target_date_str} {am_pm_str.lower()} with valid timestamps.")
        return []

    print(f"Found {len(matching_identifiers)} identifiers for {target_date_str} {am_pm_str.lower()}.")
    return matching_identifiers

def extract_cap_data(identifier):
    cap_url = f"https://publicalert.pagasa.dost.gov.ph/output/gfa/{identifier}.cap"
    cap_data = {}
    area_descriptions = []
    region_value = 'N/A'
    event_value = 'N/A'
    instruction_value = 'No specific instructions.'
    description_value = 'N/A'
    present_weather_value = 'N/A'
    rainfall_forecast_value = 'N/A'
    severity_raw_value = 'Unknown'

    try:
        response = requests.get(cap_url)
        response.raise_for_status()

        root = ET.fromstring(response.content)

        namespaces = {
            'cap': 'urn:oasis:names:tc:emergency:cap:1.2',
        }

        sent_element = root.find('cap:sent', namespaces)
        msg_type_element = root.find('cap:msgType', namespaces)
        references_element = root.find('cap:references', namespaces)
        info_element = root.find('cap:info', namespaces)

        event_element = info_element.find('cap:event', namespaces) if info_element is not None else None
        if event_element is not None and event_element.text is not None:
            event_value = event_element.text.strip()

        severity_element = info_element.find('cap:severity', namespaces) if info_element is not None else None
        severity_raw_value = severity_element.text.strip() if severity_element is not None and severity_element.text is not None else 'Unknown'

        area_elements = info_element.findall('cap:area', namespaces) if info_element is not None else []
        for area_element in area_elements:
            area_desc_element = area_element.find('cap:areaDesc', namespaces)
            if area_desc_element is not None and area_desc_element.text is not None:
                area_descriptions.append(area_desc_element.text.strip())

        instruction_element = info_element.find('cap:instruction', namespaces) if info_element is not None else None
        if instruction_element is not None and instruction_element.text is not None:
            instruction_value = instruction_element.text.strip()
            instruction_value = process_instruction_text(instruction_value)

        description_element = info_element.find('cap:description', namespaces) if info_element is not None else None
        if description_element is not None and description_element.text is not None:
            description_value = description_element.text.strip()
            description_value = process_instruction_text(description_value)

            present_weather_match = re.search(r"Under present weather conditions,(.*?)\s*The 12-hour rainfall forecast is", description_value, re.DOTALL)
            if present_weather_match:
                present_weather_value = present_weather_match.group(1).strip()

            rainfall_forecast_match = re.search(r"The 12-hour rainfall forecast is(.*?)(?:\s*WATERCOURSES (?:STILL )?LIKELY TO BE AFFECTED :|\s*$)", description_value, re.DOTALL)
            if rainfall_forecast_match:
                rainfall_forecast_value = rainfall_forecast_match.group(1).strip()

                if rainfall_forecast_value:
                    rainfall_forecast_value = rainfall_forecast_value[0].upper() + rainfall_forecast_value[1:].lower()


        parameter_elements = info_element.findall('cap:parameter', namespaces) if info_element is not None else []
        for param_element in parameter_elements:
            value_name_element = param_element.find('cap:valueName', namespaces)
            value_element = param_element.find('cap:value', namespaces)

            if value_name_element is not None and value_name_element.text is not None and \
               value_name_element.text.strip() == 'layer:Google:Region:0.1' and \
               value_element is not None and value_element.text is not None:
                region_value = value_element.text.strip()
                break

        cap_data['sent'] = sent_element.text.strip() if sent_element is not None and sent_element.text is not None else 'N/A'
        cap_data['event'] = event_value
        cap_data['areaDescs'] = area_descriptions
        cap_data['region'] = region_value
        cap_data['instruction'] = instruction_value
        cap_data['description'] = description_value
        cap_data['present_weather'] = present_weather_value
        cap_data['rainfall_forecast'] = rainfall_forecast_value
        cap_data['rivers_info_by_province'] = {}
        cap_data['severity_raw'] = severity_raw_value
        cap_data['msgType'] = msg_type_element.text.strip() if msg_type_element is not None and msg_type_element.text is not None else 'N/A'
        cap_data['references'] = references_element.text.strip() if references_element is not None and references_element.text is not None else None

        if region_value == "Region 11 (Davao Region)":
            davao_occidental_pattern = r"\+\s*\*\*Davao Occidental\*\*"
            if re.search(davao_occidental_pattern, description_value, re.DOTALL):
                if "Davao Occidental" not in area_descriptions:
                    area_descriptions.append("Davao Occidental")

        text_to_parse_watercourses = None

        watercourses_pattern = r"WATERCOURSES (?:STILL )?LIKELY TO BE AFFECTED :"

        if instruction_value and re.search(watercourses_pattern, instruction_value):
            text_to_parse_watercourses = instruction_value
        elif description_value and re.search(watercourses_pattern, description_value):
            text_to_parse_watercourses = description_value

        if text_to_parse_watercourses:
            match = re.search(watercourses_pattern, text_to_parse_watercourses)
            if match:
                start_index = match.end()
                watercourses_text = text_to_parse_watercourses[start_index:].strip()

                pattern_findall = r'\+\s*\*\*(.*?)\*\*\s*-\s*(.*?)(?=\s*\+\s*\*\*|\s*$)'
                matches = re.findall(pattern_findall, watercourses_text)

                for province_name_raw, rivers_description_raw in matches:
                    cleaned_province_name = province_name_raw.replace('Province of ', '').strip().lower()

                    cleaned_rivers_description = rivers_description_raw.replace('\xa0', ' ').strip()

                    cap_data['rivers_info_by_province'][cleaned_province_name] = cleaned_rivers_description

    except requests.exceptions.RequestException as e:
        print(f"Error fetching CAP file for identifier {identifier}: {e}")
        return None
    except ET.ParseError as e:
        print(f"Error parsing CAP file for identifier {identifier}: {e}")
        return None
    except Exception as e:
        print(f"An unexpected error occurred for identifier {identifier}: {e}")
        traceback.print_exc()
        return None

    cap_data['areaDescs'] = area_descriptions
    return cap_data

def filter_active_advisories(all_raw_gfa_data: dict) -> dict:
    cancelled_or_superseded_ids = set()
    
    for identifier, cap_data in all_raw_gfa_data.items():
        msg_type = cap_data.get('msgType')
        references_str = cap_data.get('references')
            
        if msg_type == 'Cancel':
            cancelled_or_superseded_ids.add(identifier)
            if references_str:
                parts = references_str.split(',')
                if len(parts) >= 2:
                    referred_id = parts[1].strip()
                    if re.fullmatch(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}', referred_id):
                        cancelled_or_superseded_ids.add(referred_id)
                    else:
                        print(f"Warning: Invalid ID format in references for {identifier}: '{referred_id}'. Not adding to cancelled list.")
                else:
                    print(f"Warning: Malformed references string for {identifier}: '{references_str}'.")

        elif msg_type == 'Update':
            if references_str:
                parts = references_str.split(',')
                if len(parts) >= 2:
                    referred_id = parts[1].strip()
                    if re.fullmatch(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}', referred_id):
                        cancelled_or_superseded_ids.add(referred_id)
                    else:
                        print(f"Warning: Invalid ID format in references for update {identifier}: '{referred_id}'. Not marking as superseded.")
                else:
                    print(f"Warning: Malformed references string for update {identifier}: '{references_str}'.")

    active_gfa_data = {}
    for identifier, cap_data in all_raw_gfa_data.items():
        if identifier not in cancelled_or_superseded_ids:
            active_gfa_data[identifier] = cap_data

    print(f"Identified {len(cancelled_or_superseded_ids)} CAP files (including cancellations and superseded advisories) to be excluded.")
    print(f"Remaining active advisories: {len(active_gfa_data)}")

    return active_gfa_data

def extract_basin_links(soup):
    """Extracts river basin links and their statuses from the main page."""
    basin_links, statuses = {}, {}
    for row in soup.find_all("tr"):
        columns = row.find_all("td")
        if len(columns) < 2:
            continue
        river_basin = columns[0].get_text(strip=True)
        status_element = columns[1].find("a")
        if status_element:
            status = status_element.get_text(strip=True)
            link = urljoin("https://www.pagasa.dost.gov.ph/flood", status_element["href"])
            if status == "Non-Flood Watch" and link.lower().endswith("non-flood-watch"):
                link = None
            basin_links[river_basin] = link
            statuses[river_basin] = status
    return basin_links, statuses

def extract_flood_data(basin, link, session, statuses):
    """
    Extracts flood data for a single river basin using the new regex logic.
    """
    if not link:
        return [basin, statuses.get(basin, 'N/A'), 'N/A', 'N/A', 'N/A', 'N/A', 'N/A', None]
    
    if link.lower().endswith('.pdf'):
        pdf_link_text = f'<b>Information:</b> <a href="{link}" target="_blank">{link}</a>'
        return [basin, statuses.get(basin, 'N/A'), pdf_link_text, '', '', '', '', link]
    
    soup = fetch_page(link, session)
    if not soup:
        return [basin, statuses.get(basin, 'N/A'), 'N/A', 'N/A', 'N/A', 'N/A', 'N/A', None]
    
    page_content = soup.get_text()
    issued_at = 'N/A'
    valid_until = '9:00 am tomorrow'
    observed_rainfall = 'N/A'
    forecasted_rainfall = 'N/A'
    water_level_forecast = 'N/A'
    issued_at_match = re.search(r'ISSUED AT([\s\S]+?)VALID', page_content, re.IGNORECASE)
    if issued_at_match:
        issued_at = issued_at_match.group(1).strip()
        issued_at = format_issued_at(issued_at)
    observed_rainfall_match = re.search(r'OBSERVED 24-HR RAINFALL:([\s\S]+?)(?:WAS|WERE)', page_content, re.IGNORECASE)
    if observed_rainfall_match:
        observed_rainfall = observed_rainfall_match.group(1).strip()
        observed_rainfall = to_sentence_case(observed_rainfall)
    forecasted_rainfall_match = re.search(r'FORECAST 24-HR RAINFALL:([\s\S]+?)(?=FORECAST WATER LEVEL:)', page_content, re.IGNORECASE)
    if forecasted_rainfall_match:
        forecasted_rainfall = forecasted_rainfall_match.group(1).strip()
        forecasted_rainfall = to_sentence_case(forecasted_rainfall)
        forecasted_rainfall = forecasted_rainfall.rstrip('.')
    water_level_forecast_match = re.search(r'FORECAST WATER LEVEL:([\s\S]+?)(?=PREPARED BY:)', page_content, re.IGNORECASE)
    if water_level_forecast_match:
        water_level_forecast = water_level_forecast_match.group(1).strip()
        water_level_forecast = format_water_level(water_level_forecast)
    return [basin, statuses.get(basin, 'N/A'), issued_at, valid_until, observed_rainfall, forecasted_rainfall, water_level_forecast, link]

def get_river_basin_data():
    """Main function to get river basin flood data."""
    BASE_URL = "https://www.pagasa.dost.gov.ph/flood"
    try:
        with requests.Session() as session:
            main_soup = fetch_page(BASE_URL, session)
            if not main_soup:
                print("⚠️ Failed to fetch main page.", file=sys.stderr)
                return pd.DataFrame(columns=["River Basin", "Status", "Issued at", "Valid until", "Observed 24-hour rainfall", "Forecast 24-hour rainfall", "Water Level Forecast", "Link"])
            basin_links, statuses = extract_basin_links(main_soup)
            data = [extract_flood_data(basin, link, session, statuses) for basin, link in basin_links.items()]
        df = pd.DataFrame(data, columns=["River Basin", "Status", "Issued at", "Valid until", "Observed 24-hour rainfall", "Forecast 24-hour rainfall", "Water Level Forecast", "Link"])
        return df
    except Exception as e:
        print(f"An error occurred during data extraction: {e}", file=sys.stderr)
        return pd.DataFrame(columns=["River Basin", "Status", "Issued at", "Valid until", "Observed 24-hour rainfall", "Forecast 24-hour rainfall", "Water Level Forecast", "Link"])

# 4. Map Generation and Styling Functions
# -----------------------------------------------------------------------------
def style_function(feature):
    status = feature['properties'].get('Status', 'N/A')
    if status == 'Flood Watch':
        color = '#c0392b'
    else:
        color = '#009bff'
    return {
        'fillColor': color,
        'color': color,
        'weight': 2,
        'fillOpacity': 0.4,
        'dashArray': '4, 4'
    }

def create_flood_map(gfa_data, province_geojson_path):
    map_center = [12.8797, 121.7740]
    m = folium.Map(location=map_center, zoom_start=6, tiles=None)

    # labels_on_by_default = bool(gfa_data)
    
    folium.TileLayer(
        tiles="Esri.WorldGrayCanvas",
        name="Basemap: ESRI World Gray Canvas",
        control=True
    ).add_to(m)
    folium.TileLayer(
        tiles="OpenStreetMap.Mapnik",
        name="Basemap: OpenStreetMap",
        control=True,
        show=False
    ).add_to(m)
    folium.TileLayer(
        tiles="Esri.OceanBasemap",
        name="Basemap: ESRI World Ocean Base",
        control=True,
        show=False
    ).add_to(m)
    folium.TileLayer(
        tiles="Esri.WorldImagery",
        name="Basemap: ESRI World Imagery",
        control=True,
        show=False
    ).add_to(m)

    m.get_root().html.add_child(folium.Element("<title>Flood Information | DOST-PAGASA</title>"))
    m.get_root().html.add_child(folium.Element(
        '<link rel="icon" href="https://pubfiles.pagasa.dost.gov.ph/pagasaweb/images/pagasa-logo.png" type="image/png">'
    ))

    southwest = (4, 116)
    northeast = (21.5, 127)

    province_info = {}
    
    if not gfa_data:
        print("\nNo GFA data provided. Generating a map with 'No Advisory' for all provinces.")
        provinces_gdf = gpd.read_file(province_geojson_path)
        for index, row in provinces_gdf.iterrows():
            province_name_from_geojson = row.get('adm2_en')
            if isinstance(province_name_from_geojson, str):
                cleaned_province_name_geojson_lower = province_name_from_geojson.replace('Province of ', '').strip().lower()
                province_info[cleaned_province_name_geojson_lower] = {
                    'color': 'white',
                    'severity_level': 0,
                    'event': 'No Advisory',
                    'identifier': 'N/A',
                    'region': 'N/A',
                    'sent': datetime.now().isoformat(),
                    'instruction': 'No specific instructions.',
                    'rivers_info': 'N/A',
                    'present_weather': 'N/A',
                    'rainfall_forecast': 'N/A'
                }
    else:
        for identifier, data in gfa_data.items():
            event = data.get('event', '')
            severity_raw = data.get('severity_raw', 'Unknown')
            severity_color = get_severity_color(severity_raw)
            severity_level = get_severity_level(severity_raw)
            
            area_descs = data.get('areaDescs', [])
            region = data.get('region', 'N/A')
            sent_time = data.get('sent', 'N/A')
            instruction = data.get('instruction', 'N/A')
            present_weather_data = data.get('present_weather', 'N/A')
            rainfall_forecast_data = data.get('rainfall_forecast', 'N/A')
            rivers_data_for_this_cap = data.get('rivers_info_by_province', {})

            for province_name_from_cap in area_descs:
                if isinstance(province_name_from_cap, str) and province_name_from_cap.strip():
                    cleaned_province_name_cap_lower = province_name_from_cap.replace('Province of ', '').strip().lower()
                    current_max_severity = province_info.get(cleaned_province_name_cap_lower, {}).get('severity_level', -1)

                    if severity_level > current_max_severity:
                        province_rivers_info = rivers_data_for_this_cap.get(cleaned_province_name_cap_lower, 'N/A')
                        
                        province_info[cleaned_province_name_cap_lower] = {
                            'color': severity_color,
                            'severity_level': severity_level,
                            'event': event,
                            'identifier': identifier,
                            'region': region,
                            'sent': sent_time,
                            'instruction': instruction,
                            'present_weather': present_weather_data,
                            'rainfall_forecast': rainfall_forecast_data,
                            'rivers_info': province_rivers_info
                        }

    try:
        provinces_gdf = gpd.read_file(province_geojson_path)
    except FileNotFoundError:
        print(f"\nError: Province GeoJSON file not found at {province_geojson_path}")
        print("Please provide a valid path to a GeoJSON file containing Philippine province boundaries.")
        print("You can try searching online for 'Philippine provinces GeoJSON'.")
        return
    except Exception as e:
        print(f"\nError loading or processing GeoJSON file: {e}")
        traceback.print_exc()
        return

    provinces_by_gfa_type_for_summary = {}
    for cleaned_prov_name_lower, info in province_info.items():
        original_province_name = next((
            feature['properties']['adm2_en'] for feature in provinces_gdf.iterfeatures()
            if feature['properties'].get('adm2_en', '').replace('Province of ', '').strip().lower() == cleaned_prov_name_lower
        ), cleaned_prov_name_lower.title())

        province_region_name = info.get('region', 'N/A Region')
        province_region_sort_key = region_order_map.get(province_region_name, 999)

        display_summary_event_text = info['event']
        if 'moderate' in info['event'].lower():
            display_summary_event_text = 'Flood Monitoring'
        elif 'severe' in info['event'].lower():
            display_summary_event_text = 'Flood Alert'
        elif 'extreme' in info['event'].lower():
            display_summary_event_text = 'Flood Warning'
        elif 'final' in info['event'].lower():
            display_summary_event_text = 'Final Advisory'
        elif 'no advisory' in info['event'].lower():
            display_summary_event_text = 'No Advisory'

        if display_summary_event_text not in provinces_by_gfa_type_for_summary:
            provinces_by_gfa_type_for_summary[display_summary_event_text] = []
        provinces_by_gfa_type_for_summary[display_summary_event_text].append((province_region_sort_key, original_province_name))

    sorted_provinces_by_gfa_type = {}
    for gfa_type in gfa_category_order:
        if gfa_type in provinces_by_gfa_type_for_summary:
            provinces_for_gfa_type = provinces_by_gfa_type_for_summary[gfa_type]

            provinces_for_gfa_type.sort(key=lambda x: (x[0], x[1]))

            sorted_province_names_only = [prov_name for _, prov_name in provinces_for_gfa_type]
            sorted_provinces_by_gfa_type[gfa_type] = sorted_province_names_only
            
    issued_date_time_part = "N/A"
    validity_info_part = ""
    is_standard_time = False

    if gfa_data and any(gfa_data.values()):
        latest_sent_time = None
        for data in gfa_data.values():
            sent = data.get('sent')
            if sent != 'N/A':
                try:
                    current_sent_dt = datetime.strptime(sent, '%Y-%m-%dT%H:%M:%S%z')
                    if latest_sent_time is None or current_sent_dt > latest_sent_time:
                        latest_sent_time = current_sent_dt
                except ValueError:
                    pass
        if latest_sent_time:
            issued_date_time_part, validity_info_part, is_standard_time = format_issued_time(latest_sent_time.isoformat())

    df_forecast = get_river_basin_data()
    df_forecast['River Basin'] = df_forecast['River Basin'].str.strip().str.replace(r'\s{2,}', ' ', regex=True)
    df_forecast['is_subbasin'] = df_forecast['River Basin'].str.contains('Sub-basin', case=False)
    df_forecast['Island Group'] = df_forecast['River Basin'].map(island_groups).fillna('Others')
    df_forecast['status_order'] = df_forecast['Status'].map({'Flood Watch': 0, 'Non-Flood Watch': 1})
    df_forecast['island_group_order'] = df_forecast['Island Group'].astype('category').cat.set_categories(island_group_order, ordered=True)
    sorted_basins = df_forecast.sort_values(by=['status_order', 'island_group_order', 'is_subbasin', 'River Basin'], ascending=[True, True, True, True])
    flood_watch_basins = sorted_basins[sorted_basins['Status'] == 'Flood Watch']
    non_flood_watch_basins = sorted_basins[sorted_basins['Status'] == 'Non-Flood Watch']

    if not df_forecast.empty:
        for _, row in df_forecast.iterrows():
            if 'http' not in str(row['Issued at']) and str(row['Issued at']) != 'N/A':
                break
    list_sections_html = ""
    if len(flood_watch_basins) > 0:
        list_sections_html += f"""
            <div style="background-color: #C0392B; color: white; padding: 6px; border-radius: 4px; font-weight: bold; margin-bottom: 5px; font-size: 14px;">
                Flood Watch
                <div style="font-size: 12px; font-weight: normal; margin-top: 2px; line-height: 1.2">
                    River flooding is POSSIBLE. Click the river basin name for the full warning.
                </div>
            </div>
            {generate_grouped_list_html(flood_watch_basins, '#C0392B', '14px')}
        """
    if len(non_flood_watch_basins) > 0:
        list_sections_html += f"""
            <div style="background-color: #009BFF; color: white; padding: 6px; border-radius: 4px; font-weight: bold; margin-bottom: 5px; font-size: 14px;">
                Non-Flood Watch
                <div style="font-size: 12px; font-weight: normal; margin-top: 2px; line-height: 1.2">
                    River flooding is not expected, but flooding in low-lying, poorly drained, or coastal areas is still possible due to thunderstorms and/or tides.
                </div>
            </div>
            {generate_grouped_list_html(non_flood_watch_basins, '#009BFF', '12px')}
        """

    provinces_gdf['tooltip_html_content'] = provinces_gdf.apply(
        lambda row: generate_tooltip_html(
            {'properties': row.to_dict()},
            province_info
        ), axis=1
    )

    map_styled_province_function = get_styled_province_function(province_info)

    tooltip_field = folium.features.GeoJsonTooltip(
        fields=['tooltip_html_content'],
        aliases=[''],
        localize=False,
        sticky=True,
        labels=False,
        max_width=800
    )

    folium.GeoJson(
        provinces_gdf,
        name='Provinces under Active GFAs',
        style_function=map_styled_province_function,
        tooltip=tooltip_field
    ).add_to(m)

    province_labels_group = folium.FeatureGroup(name="Provinces under Active GFAs (Labels)", show=False)
    province_labels_group.add_to(m)

    if gfa_data and any(info['color'] != 'white' for info in province_info.values()):
        for index, row in provinces_gdf.iterrows():
            province_name = row['adm2_en']
            if isinstance(province_name, str):
                cleaned_province_name_lower = province_name.replace('Province of ', '').strip().lower()
    
                if cleaned_province_name_lower in province_info and province_info[cleaned_province_name_lower]['color'] != 'white':
                    label_lat = row.get('label_lat')
                    label_lon = row.get('label_lon')
    
                    final_label_coords = None
    
                    if pd.notna(label_lat) and pd.notna(label_lon):
                        try:
                            final_label_coords = [float(label_lat), float(label_lon)]
                        except ValueError:
                            print(f"Warning: Non-numeric label_lat/lon for {province_name}. Falling back to polylabel.")
                            final_label_coords = None
                    else:
                        print(f"Info: Missing label_lat/lon for {province_name}. Falling back to polylabel.")
                    
                    if final_label_coords is None:
                        if row.geometry:
                            geometry_for_label = None
    
                            if not row.geometry.is_valid:
                                try:
                                    repaired_geometry = make_valid(row.geometry)
                                    if repaired_geometry and not repaired_geometry.is_empty and repaired_geometry.is_valid:
                                        geometry_for_label = repaired_geometry
                                except Exception as e:
                                    print(f"Error repairing geometry for {province_name}: {e}")
                                    geometry_for_label = None
                            else:
                                geometry_for_label = row.geometry
    
                            if geometry_for_label and geometry_for_label.is_valid:
                                label_point = None
                                try:
                                    if geometry_for_label.geom_type == 'Polygon':
                                        label_point = polylabel(geometry_for_label, tolerance=0.001)
                                    elif geometry_for_label.geom_type == 'MultiPolygon':
                                        largest_part = None
                                        max_area = -1
                                        for part in geometry_for_label.geoms:
                                            if isinstance(part, Polygon) and part.is_valid:
                                                part_area = part.area
                                                if part_area > max_area:
                                                    largest_part = part
                                                    max_area = part_area
                                        if largest_part:
                                            label_point = polylabel(largest_part, tolerance=0.001)
    
                                    if isinstance(label_point, Point):
                                        final_label_coords = [label_point.y, label_point.x]
                                    else:
                                        print(f"Warning: polylabel returned non-Point for {province_name}. Skipping label.")
                                except Exception as e:
                                    print(f"Error calculating polylabel for {province_name}: {e}")
                                    pass
                    
                    if final_label_coords:
                        label_html = f'<div style="font-size: 8pt; color: black; text-align: center; white-space: nowrap; text-shadow: -1px -1px 0 #FFF, 1px -1px 0 #FFF, -1px 1px 0 #FFF, 1px 1px 0 #FFF;">{province_name}</div>'
    
                        folium.Marker(
                            location=final_label_coords,
                            icon=folium.DivIcon(
                                html=label_html,
                                class_name="province-label",
                                icon_size=(120, 20),
                                icon_anchor=(60, 10)
                            ),
                        ).add_to(province_labels_group)
                    else:
                        print(f"Skipping label for {province_name} due to missing or invalid coordinates (no custom and no valid polylabel).")

    full_viewport_css = """
    <style>
        html, body {
            width: 100%;
            height: 100%;
            margin: 0;
            padding: 0;
            overflow: hidden;
        }
        .folium-map {
            position: absolute;
            top: 0;
            left: 0;
            width: 100% !important;
            height: 100% !important;
        }
    </style>
    """
    m.get_root().html.add_child(folium.Element(full_viewport_css))
    
    province_label_css = """
    <style>
        .province-label {
        }
        .province-label div {
            position: relative;
            transform: translate(-50%, -50%);
            left: 50%;
            top: 50%;
            font-size: 8pt;
            color: black;
            text-align: center;
            white-space: normal;
            max-width: 100px;
            text-shadow: -1px -1px 0 #FFF, 1px -1px 0 #FFF, -1px 1px 0 #FFF, 1px 1px 0 #FFF;
        }
    </style>
    """
    m.get_root().html.add_child(folium.Element(province_label_css))
    
    gdf_rb = gpd.read_file("rb.geojson")
    if 'Name' not in gdf_rb.columns:
        print("Error: 'rb.geojson' does not contain a column named 'Name'. Please check the file.", file=sys.stderr)
        exit()
    gdf_rb = gdf_rb.merge(df_forecast, left_on="Name", right_on="River Basin", how="left")
    # gdf_rb = gdf_rb.fillna('N/A')
    geojson_rb = folium.GeoJson(
        gdf_rb,
        name='18 Major River Basins',
        style_function=style_function
    )
    geojson_rb.add_to(m)
    labels_layer = folium.features.FeatureGroup(name='18 Major River Basins (Labels)', show=False).add_to(m)
    for _, r in gdf_rb.iterrows():
        status = r['Status']
        
        # Determine shadow color based on status
        if status == 'Flood Watch':
            shadow_color = '#c0392b'
        else:
            shadow_color = '#009bff'

        italic_style = ''
        if 'Sub-basin' in r['Name']:
            italic_style = 'font-style: italic;'

        # Generate unique CSS for this label's shadow
        label_css = f"""
        <style>
          .river-basin-label-{r.name} {{
            font-family: Arial, sans-serif;
            font-size: 8pt;
            font-weight: regular;
            color: black;
            text-shadow:
              -0.4px -0.4px 0 {shadow_color},
              0.4px -0.4px 0 {shadow_color},
              -0.4px 0.4px 0 {shadow_color},
              0.4px 0.4px 0 {shadow_color};
            white-space: normal;
            max-width: 100px;
            text-align: center;
            transform: translate(-50%, -50%);
            {italic_style}
          }}
        </style>
        """
        m.get_root().html.add_child(folium.Element(label_css))
        
        html = f'<div class="river-basin-label-{r.name}">{r["Name"]}</div>'
        labels_layer.add_child(
            folium.map.Marker(
                location=[r['label_lat'], r['label_lon']],
                icon=folium.DivIcon(
                    icon_size=(150,36),
                    icon_anchor=(0,0),
                    html=html,
                    class_name="dummy"
                )
            )
        )

        geojson_feature = {
            'type': 'Feature',
            'geometry': r.geometry.__geo_interface__,
            'properties': r.drop('geometry').to_dict()
        }
        if '<b>Information:</b>' in r['Issued at']:
            content_html = f"""
            <b>River Basin:</b> {r['Name']}<br>
            <b>Status:</b> {format_status_badge(r['Status'])}<br>
            {r['Issued at']}
            """
        else:
            link_html = f'<b>Information:</b> <a href="{r["Link"]}" target="_blank">{r["Link"]}</a>' if r['Link'] else ''
            content_html = f"""
            <b>River Basin:</b> {r['Name']}<br>
            <b>Status:</b> {format_status_badge(r['Status'])}<br>
            <b>Issued at:</b> {r['Issued at']}<br>
            <b>Valid until:</b> {r['Valid until']}<br>
            <b>Observed 24-hour rainfall:</b> {r['Observed 24-hour rainfall']}<br>
            <b>Forecast 24-hour rainfall:</b> {r['Forecast 24-hour rainfall']}<br>
            <b>Water Level Forecast:</b><br>
            {r['Water Level Forecast']}<br>
            {link_html}
            """
        folium_geojson = folium.GeoJson(geojson_feature, style_function=style_function)
        folium_geojson.add_child(folium.Tooltip(content_html, max_width=450))
        folium_geojson.add_child(folium.Popup(content_html, max_width=450))
        folium_geojson.add_to(geojson_rb)

    move_zoom_control_js_html = f"""
    <style>
        .leaflet-control-zoom a {{
            display: flex;
            justify-content: center;
            align-items: center;
            text-decoration: none;
            font-weight: bold;
            font-size: 1.2em;
        }}

        .leaflet-control-zoom-in,
        .leaflet-control-zoom-out {{
            line-height: normal !important;
        }}
    </style>
    <script>
        document.addEventListener('DOMContentLoaded', function() {{
            var checkExist = setInterval(function() {{
                var zoomControl = document.querySelector('.leaflet-control-zoom');
                if (zoomControl) {{
                    clearInterval(checkExist); // Stop the polling
                    var controlContainer = zoomControl.parentNode;
                    if (controlContainer) {{
                        controlContainer.style.position = 'absolute';
                        controlContainer.style.bottom = '24px';
                        controlContainer.style.right = '10px';
                        controlContainer.style.top = 'auto';
                        controlContainer.style.left = 'auto';
                        console.log('Zoom control repositioned.');
                    }}
                }} else {{
                    console.log('Waiting for zoom control...');
                }}
            }}, 50); // Check every 50 milliseconds
        }});
    </script>
    """
    m.get_root().html.add_child(folium.Element(move_zoom_control_js_html))
    
    folium.LayerControl().add_to(m)
    m.fit_bounds([southwest, northeast])
    return m

def inject_sidebar_html(file_path, gfa_data, province_geojson_path):
    province_info = {}
    
    if not gfa_data:
        print("\nNo GFA data provided. Generating a map with 'No Advisory' for all provinces.")
        provinces_gdf = gpd.read_file(province_geojson_path)
        for index, row in provinces_gdf.iterrows():
            province_name_from_geojson = row.get('adm2_en')
            if isinstance(province_name_from_geojson, str):
                cleaned_province_name_geojson_lower = province_name_from_geojson.replace('Province of ', '').strip().lower()
                province_info[cleaned_province_name_geojson_lower] = {
                    'color': 'white',
                    'severity_level': 0,
                    'event': 'No Advisory',
                    'identifier': 'N/A',
                    'region': 'N/A',
                    'sent': datetime.now().isoformat(),
                    'instruction': 'No specific instructions.',
                    'rivers_info': 'N/A',
                    'present_weather': 'N/A',
                    'rainfall_forecast': 'N/A'
                }
    else:
        for identifier, data in gfa_data.items():
            event = data.get('event', '')
            severity_raw = data.get('severity_raw', 'Unknown')
            severity_color = get_severity_color(severity_raw)
            severity_level = get_severity_level(severity_raw)
            
            area_descs = data.get('areaDescs', [])
            region = data.get('region', 'N/A')
            sent_time = data.get('sent', 'N/A')
            instruction = data.get('instruction', 'N/A')
            present_weather_data = data.get('present_weather', 'N/A')
            rainfall_forecast_data = data.get('rainfall_forecast', 'N/A')
            rivers_data_for_this_cap = data.get('rivers_info_by_province', {})

            for province_name_from_cap in area_descs:
                if isinstance(province_name_from_cap, str) and province_name_from_cap.strip():
                    cleaned_province_name_cap_lower = province_name_from_cap.replace('Province of ', '').strip().lower()
                    current_max_severity = province_info.get(cleaned_province_name_cap_lower, {}).get('severity_level', -1)

                    if severity_level > current_max_severity:
                        province_rivers_info = rivers_data_for_this_cap.get(cleaned_province_name_cap_lower, 'N/A')
                        
                        province_info[cleaned_province_name_cap_lower] = {
                            'color': severity_color,
                            'severity_level': severity_level,
                            'event': event,
                            'identifier': identifier,
                            'region': region,
                            'sent': sent_time,
                            'instruction': instruction,
                            'present_weather': present_weather_data,
                            'rainfall_forecast': rainfall_forecast_data,
                            'rivers_info': province_rivers_info
                        }

    try:
        provinces_gdf = gpd.read_file(province_geojson_path)
    except FileNotFoundError:
        print(f"\nError: Province GeoJSON file not found at {province_geojson_path}")
        print("Please provide a valid path to a GeoJSON file containing Philippine province boundaries.")
        print("You can try searching online for 'Philippine provinces GeoJSON'.")
        return
    except Exception as e:
        print(f"\nError loading or processing GeoJSON file: {e}")
        traceback.print_exc()
        return

    event_details = {
        "Flood Warning": {
            'text': 'Take appropriate actions immediately.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/flood-warning.png'
        },
        "Flood Alert": {
            'text': 'Be alert for possible flashfloods and landslides.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/flood-alert.png'
        },
        "Flood Monitoring": {
            'text': 'Take necessary precautionary measures.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/flood-monitoring.png'
        },
        "Final Advisory": {
            'text': 'Flood is no longer likely unless significant rain occurs.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/final.png'
        }
    }

    provinces_by_gfa_type_for_summary = {}
    for cleaned_prov_name_lower, info in province_info.items():
        original_province_name = next((
            feature['properties']['adm2_en'] for feature in provinces_gdf.iterfeatures()
            if feature['properties'].get('adm2_en', '').replace('Province of ', '').strip().lower() == cleaned_prov_name_lower
        ), cleaned_prov_name_lower.title())

        province_region_name = info.get('region', 'N/A Region')
        province_region_sort_key = region_order_map.get(province_region_name, 999)

        display_summary_event_text = info['event']
        if 'moderate' in info['event'].lower():
            display_summary_event_text = 'Flood Monitoring'
        elif 'severe' in info['event'].lower():
            display_summary_event_text = 'Flood Alert'
        elif 'extreme' in info['event'].lower():
            display_summary_event_text = 'Flood Warning'
        elif 'final' in info['event'].lower():
            display_summary_event_text = 'Final Advisory'
        elif 'no advisory' in info['event'].lower():
            display_summary_event_text = 'No Advisory'

        if display_summary_event_text not in provinces_by_gfa_type_for_summary:
            provinces_by_gfa_type_for_summary[display_summary_event_text] = []
        provinces_by_gfa_type_for_summary[display_summary_event_text].append((province_region_sort_key, original_province_name))

    sorted_provinces_by_gfa_type = {}
    for gfa_type in gfa_category_order:
        if gfa_type in provinces_by_gfa_type_for_summary:
            provinces_for_gfa_type = provinces_by_gfa_type_for_summary[gfa_type]

            provinces_for_gfa_type.sort(key=lambda x: (x[0], x[1]))

            sorted_province_names_only = [prov_name for _, prov_name in provinces_for_gfa_type]
            sorted_provinces_by_gfa_type[gfa_type] = sorted_province_names_only
            
    issued_date_time_part = "N/A"
    validity_info_part = ""
    is_standard_time = False

    if gfa_data and any(gfa_data.values()):
        latest_sent_time = None
        for data in gfa_data.values():
            sent = data.get('sent')
            if sent != 'N/A':
                try:
                    current_sent_dt = datetime.strptime(sent, '%Y-%m-%dT%H:%M:%S%z')
                    if latest_sent_time is None or current_sent_dt > latest_sent_time:
                        latest_sent_time = current_sent_dt
                except ValueError:
                    pass
        if latest_sent_time:
            issued_date_time_part, validity_info_part, is_standard_time = format_issued_time(latest_sent_time.isoformat())
    else:
        if user_am_pm_input == 'am':
            time_part = "6:00 am"
        else:
            time_part = "6:00 pm"
        
        user_date_obj = datetime.strptime(user_date_input, '%Y-%m-%d')
        date_part = user_date_obj.strftime("%d %B %Y")
        
        issued_date_time_part = f"{time_part}, {date_part}"
        validity_info_part = ""
        is_standard_time = True
        
    gfa_provinces_summary_text = format_gfa_provinces(sorted_provinces_by_gfa_type, event_details, issued_date_time_part, validity_info_part)

    df_forecast = get_river_basin_data()
    df_forecast['River Basin'] = df_forecast['River Basin'].str.strip().str.replace(r'\s{2,}', ' ', regex=True)
    df_forecast['is_subbasin'] = df_forecast['River Basin'].str.contains('Sub-basin', case=False)
    df_forecast['Island Group'] = df_forecast['River Basin'].map(island_groups).fillna('Others')
    df_forecast['status_order'] = df_forecast['Status'].map({'Flood Watch': 0, 'Non-Flood Watch': 1})
    df_forecast['island_group_order'] = df_forecast['Island Group'].astype('category').cat.set_categories(island_group_order, ordered=True)
    sorted_basins = df_forecast.sort_values(by=['status_order', 'island_group_order', 'is_subbasin', 'River Basin'], ascending=[True, True, True, True])
    flood_watch_basins = sorted_basins[sorted_basins['Status'] == 'Flood Watch']
    non_flood_watch_basins = sorted_basins[sorted_basins['Status'] == 'Non-Flood Watch']
    if not df_forecast.empty:
        for _, row in df_forecast.iterrows():
            if 'http' not in str(row['Issued at']) and str(row['Issued at']) != 'N/A':
                break
    list_sections_html = ""
    if len(flood_watch_basins) > 0:
        list_sections_html += f"""
                <div style="
                    font-size: 24px;
                    display: flex;
                    align-items: center;
                    width: 100%;
                    text-align: left;
                    padding: 4px 8px 5px 8px;
                    border-radius: 3px;
                    background-color: #C0392B;
                    color: white;
                    font-weight: bold;
                ">
                    <div style="margin-top: 2px; margin-right: 8px; margin-left: 2px;">
                        <i class="fa-solid fa-triangle-exclamation"></i>
                    </div>
                    <div style="flex-grow: 1; font-size: 14px">
                        Flood Watch
                        <div style="font-size: 12px; font-weight: normal; line-height: 1.2;">
                        River flooding is POSSIBLE. Click the river basin name for the full warning.
                        </div>
                    </div>
                </div>
            {generate_grouped_list_html(flood_watch_basins, '#C0392B', '14px')}
        """
    if len(non_flood_watch_basins) > 0:
        list_sections_html += f"""
                <div style="
                    font-size: 24px;
                    display: flex;
                    align-items: center;
                    width: 100%;
                    text-align: left;
                    padding: 4px 8px 5px 8px;
                    border-radius: 3px;
                    background-color: #009BFF;
                    color: white;
                    font-weight: bold;
                ">
                    <div style="margin-top: 2px; margin-right: 8px; margin-left: 2px;">
                        <i class="fa-solid fa-circle-info"></i>
                    </div>
                    <div style="flex-grow: 1; font-size: 14px">
                        Non-Flood Watch
                        <div style="font-size: 12px; font-weight: normal; line-height: 1.2;">
                        River flooding is not expected, but flooding in low-lying, poorly drained, or coastal areas is still possible due to thunderstorms and/or tides.
                        </div>
                    </div>
                </div>
            {generate_grouped_list_html(non_flood_watch_basins, '#009BFF', '12px')}
        """

    if gfa_data:
        # New tabbed infobox implementation (with mockup design)
        sidebar_html = f"""
        <div id="sidebar" class="sidebar">
          <div class="sidebar-content">
            <div id="TabbedInfoContainer" style="
                position: absolute;
                top: 10px;
                left: 10px;
                z-index: 1002;
                font-family: Arial, sans-serif;
            ">
                <div id="GFAInfoBox" class="infobox-content" style="
                    background-color: white;
                    width: 364px;
                ">
                    <div style="">
                        <div style="display: flex; align-items: center; width: 100%; margin-bottom: 4px;">
                            <img src="https://pubfiles.pagasa.dost.gov.ph/pagasaweb/images/pagasa-logo.png" alt="PAGASA Logo" style="width: 44px; height: 44px; margin-right: 8px;">
                            <div style="display: flex; flex-direction: column;">
                                <span style="font-size: 14px; font-weight: bold; color: #333;">DOST-PAGASA</span>
                                <span style="font-size: 14px; color: #555;">Flood Forecasting and Warning Center</span>
                            </div>
                        </div>
                        <div style="display: flex; flex-direction: column; width: 100%; margin-bottom: 4px;">
                            <span style="font-size: 24px; font-weight: bold; color: #333; margin-top: 2px">General Flood Advisories</span>
                            <span style="font-size: 14px; color: #333;">As of: {issued_date_time_part}</span>
                            <span style="font-size: 11px; color: #333;">({validity_info_part})</span>
                        </div>
                        <div id="gfaSummaryContent" style="
                            font-size: 14px;
                            max-height: calc(100vh - 20px);
                            overflow-y: auto;
                            box-sizing: border-box;
                            width: 100%;
                            display: block;
                            transition: max-height 0.3s ease-in-out;
                        ">
                            {gfa_provinces_summary_text}
                        </div>
                    </div>
                </div>
    
                <div id="RBInfoBox" class="infobox-content" style="
                    background-color: white;
                    width: 364px;
                    display: none;
                ">
                    <div style="">
                        <div style="display: flex; align-items: center; width: 100%; margin-bottom: 4px;">
                            <img src="https://pubfiles.pagasa.dost.gov.ph/pagasaweb/images/pagasa-logo.png" alt="PAGASA Logo" style="width: 44px; height: 44px; margin-right: 8px;">
                            <div style="display: flex; flex-direction: column;">
                                <span style="font-size: 14px; font-weight: bold; color: #333;">DOST-PAGASA</span>
                                <span style="font-size: 14px; color: #555;">Flood Forecasting and Warning Center</span>
                            </div>
                        </div>
                        <div style="display: flex; flex-direction: column; width: 100%; margin-bottom: 4px;">
                            <span style="font-size: 24px; font-weight: bold; color: #333; margin-top: 2px">River Basin Flood Information</span>
                            <span style="font-size: 14px; color: #333;">As of: {issued_date_time_part}</span>
                            <span style="font-size: 11px; color: #333;">(Valid until the specified time and date in the issuance)</span>
                        </div>
                        <div id="rbSummaryContent" style="
                            font-size: 14px;
                            max-height: calc(100vh - 20px);
                            overflow-y: auto;
                            box-sizing: border-box;
                            width: 100%;
                            display: block;
                            transition: max-height 0.3s ease-in-out;
                            margin-top: 12px;
                        ">
                            {list_sections_html}
                        </div>
                    </div>
                </div>
            </div>
          </div>
          <button class="gfa_tab" id="gfa_tab" title="Show General Flood Advisories" onclick="openTab(event, 'gfa_tab')">General Flood Advisories</button>
          <button class="rb_tab" id="rb_tab" title="Show River Basin Flood Information" onclick="openTab(event, 'rb_tab')">River Basin Flood Information</button>
        </div>
        <button class="openbtn" id="openbtn" title="Hide Sidebar" onclick="toggleSidebar()"><i class="fa-solid fa-angle-left"></i></button>
        """

    else:
        # Code for when no GFA data exists
        sidebar_html = f"""
        <div id="sidebar" class="sidebar">
          <div class="sidebar-content">
            <div id="TabbedInfoContainer" style="
                position: absolute;
                top: 10px;
                left: 10px;
                z-index: 1002;
                font-family: Arial, sans-serif;
            ">
                <div id="GFAInfoBox" class="infobox-content" style="
                    background-color: white;
                    width: 364px;
                ">
                    <div style="">
                        <div style="display: flex; align-items: center; width: 100%; margin-bottom: 4px;">
                            <img src="https://pubfiles.pagasa.dost.gov.ph/pagasaweb/images/pagasa-logo.png" alt="PAGASA Logo" style="width: 44px; height: 44px; margin-right: 8px;">
                            <div style="display: flex; flex-direction: column;">
                                <span style="font-size: 14px; font-weight: bold; color: #333;">DOST-PAGASA</span>
                                <span style="font-size: 14px; color: #555;">Flood Forecasting and Warning Center</span>
                            </div>
                        </div>
                        <div style="display: flex; flex-direction: column; width: 100%; margin-bottom: 4px;">
                            <span style="font-size: 24px; font-weight: bold; color: #333; margin-top: 2px">General Flood Advisories</span>
                            <span style="font-size: 14px; color: #333;">As of: {issued_date_time_part}</span>
                        </div>
                        <div id="gfaSummaryContent" style="
                            font-size: 14px;
                            max-height: calc(100vh - 20px);
                            overflow-y: auto;
                            box-sizing: border-box;
                            width: 100%;
                            display: block;
                            transition: max-height 0.3s ease-in-out;
                        ">
                            {gfa_provinces_summary_text}
                        </div>
                    </div>
                </div>
    
                <div id="RBInfoBox" class="infobox-content" style="
                    background-color: white;
                    width: 364px;
                    display: none;
                ">
                    <div style="">
                        <div style="display: flex; align-items: center; width: 100%; margin-bottom: 4px;">
                            <img src="https://pubfiles.pagasa.dost.gov.ph/pagasaweb/images/pagasa-logo.png" alt="PAGASA Logo" style="width: 44px; height: 44px; margin-right: 8px;">
                            <div style="display: flex; flex-direction: column;">
                                <span style="font-size: 14px; font-weight: bold; color: #333;">DOST-PAGASA</span>
                                <span style="font-size: 14px; color: #555;">Flood Forecasting and Warning Center</span>
                            </div>
                        </div>
                        <div style="display: flex; flex-direction: column; width: 100%; margin-bottom: 4px;">
                            <span style="font-size: 24px; font-weight: bold; color: #333; margin-top: 2px">River Basin Flood Information</span>
                            <span style="font-size: 14px; color: #333;">As of: {issued_date_time_part}</span>
                            <span style="font-size: 11px; color: #333;">(Valid until the specified time and date in the issuance)</span>
                        </div>
                        <div id="rbSummaryContent" style="
                            font-size: 14px;
                            max-height: calc(100vh - 20px);
                            overflow-y: auto;
                            box-sizing: border-box;
                            width: 100%;
                            display: block;
                            transition: max-height 0.3s ease-in-out;
                            margin-top: 12px;
                        ">
                            {list_sections_html}
                        </div>
                    </div>
                </div>
            </div>
          </div>
          <button class="gfa_tab" id="gfa_tab" title="Show General Flood Advisories" onclick="openTab(event, 'gfa_tab')">General Flood Advisories</button>
          <button class="rb_tab" id="rb_tab" title="Show River Basin Flood Information" onclick="openTab(event, 'rb_tab')">River Basin Flood Information</button>
        </div>
        <button class="openbtn" id="openbtn" title="Hide Sidebar" onclick="toggleSidebar()"><i class="fa-solid fa-angle-left"></i></button>
        """

    sidebar_css = """
    <style>
    body, html {
        height: 100%;
        margin: 0;
        padding: 0;
        overflow: hidden;
    }
    .sidebar {
      height: 100%;
      width: 384px;
      position: fixed;
      top: 0;
      left: 0;
      background-color: #fff;
      overflow-x: hidden;
      z-index: 1002;
      color: white;
      transition: transform 0.5s ease-in-out;
      border-right: 2px solid rgba(0,0,0,0.35);
    }
    .sidebar.open {
      left: 0;
    }
    .sidebar-content {
      padding: 15px;
      font-size: 24px;
      color: black;
    }
    .leaflet-control-layers {
      z-index: 1001;
    }
    .openbtn {
      font-size: 24px;
      cursor: pointer;
      background-color: #fff;
      color: black;
      padding: 12px 3px 12px 3px;
      border-left: 2px solid white;
      border-top: 2px solid rgba(0,0,0,0.35);
      border-right: 2px solid rgba(0,0,0,0.35);
      border-bottom: 2px solid rgba(0,0,0,0.35);
      position: fixed;
      top: 8px;
      left: 382px;
      z-index: 1003;
      border-radius: 0 4px 4px 0;
      transition: transform 0.5s ease-in-out;
    }
    .gfa_tab {
      background-color: #bfbfbf;
      color: #333;
      border-left: 2px solid rgba(0,0,0,0.125);
      border-top: 2px solid rgba(0,0,0,0.125);
      border-right: 2px solid rgba(0,0,0,0.125);
      border-bottom: 2px solid rgba(0,0,0,0.13);
      outline: none;
      cursor: pointer;
      padding: 2px 8px 2px 8px;
      font-size: 12px;
      position: fixed;
      top: 76px;
      left: 407px;
      width: 160px;
      transform: rotate(90deg);
      transform-origin: 0% 0%;
      z-index: 1003;
      border-radius: 4px 4px 0 0;
      transition: transform 0.5s ease-in-out;
    }
    .rb_tab {
      background-color: #bfbfbf;
      color: #333;
      border-left: 2px solid rgba(0,0,0,0.125);
      border-top: 2px solid rgba(0,0,0,0.125);
      border-right: 2px solid rgba(0,0,0,0.125);
      border-bottom: 2px solid rgba(0,0,0,0.13);
      outline: none;
      cursor: pointer;
      padding: 2px 8px 2px 8px;
      font-size: 12px;
      position: fixed;
      top: 242px;
      left: 407px;
      width: 180px;
      transform: rotate(90deg);
      transform-origin: 0% 0%;
      z-index: 1003;
      border-radius: 4px 4px 0 0;
      transition: transform 0.5s ease-in-out;
    }
    .openbtn:hover {
      background-color: #bfbfbf;
      border-left: 2px solid #bfbfbf;
      border-top: 2px solid rgba(0,0,0,0.35);
      border-right: 2px solid rgba(0,0,0,0.35);
      border-bottom: 2px solid rgba(0,0,0,0.35);
    }
    .gfa_tab:hover {
      background-color: #fff;
      color: #333;
      border-left: 2px solid rgba(0,0,0,0.35);
      border-top: 2px solid rgba(0,0,0,0.35);
      border-right: 2px solid rgba(0,0,0,0.35);
      border-bottom: 2px solid rgba(0,0,0,0.35);
    }
    .rb_tab:hover {
      background-color: #fff;
      color: #333;
      border-left: 2px solid rgba(0,0,0,0.35);
      border-top: 2px solid rgba(0,0,0,0.35);
      border-right: 2px solid rgba(0,0,0,0.35);
      border-bottom: 2px solid rgba(0,0,0,0.35);
    }
    .gfa_tab.active-tab {
      background-color: #fff;
      color: #009bff;
      border-left: 2px solid rgba(0,0,0,0.35);
      border-top: 2px solid rgba(0,0,0,0.35);
      border-right: 2px solid rgba(0,0,0,0.35);
      border-bottom: 3px solid #009bff;
      padding: 2px 8px 1px 8px;
    }
    .rb_tab.active-tab {
      background-color: #fff;
      color: #009bff;
      border-left: 2px solid rgba(0,0,0,0.35);
      border-top: 2px solid rgba(0,0,0,0.35);
      border-right: 2px solid rgba(0,0,0,0.35);
      border-bottom: 3px solid #009bff;
      padding: 2px 8px 1px 8px;
    }
    .folium-map {
        position: absolute;
        top: 0;
        left: 0;
        width: 100vw;
        height: 100vh;
    }
    .basin-list li {
      break-inside: avoid;
    }
    </style>
    """

    sidebar_js = """
    <script>
        var map;
        var gfaLayers = [];
        var rbLayers = [];
    
        // This function dynamically finds the map and layer objects on page load.
        function initializeMapAndLayers() {
            // Find the main map object by searching for a variable that starts with 'map_'
            for (const prop in window) {
                if (prop.startsWith('map_')) {
                    map = window[prop];
                    break;
                }
            }
            
            if (!map) {
                console.error("Folium map object not found.");
                return;
            }
    
            // Find the layers object by searching for a variable that starts with 'layer_control_' and ends with '_layers'
            let layerData;
            for (const prop in window) {
                if (prop.startsWith('layer_control_') && prop.endsWith('_layers')) {
                    layerData = window[prop].overlays;
                    break;
                }
            }
    
            if (!layerData) {
                console.error("Folium layer data object not found.");
                return;
            }
            
            // Loop through the found layer data to populate our layer arrays
            for (const key in layerData) {
                if (key.includes("Provinces under Active GFAs")) {
                    gfaLayers.push(layerData[key]);
                } else if (key.includes("18 Major River Basins")) {
                    rbLayers.push(layerData[key]);
                }
            }
        }
    
        function toggleSidebar() {
          // (Your existing toggleSidebar code here)
          var sidebar = document.getElementById("sidebar");
          if (sidebar.style.left === '0px') {
              sidebar.style.left = '-384px';
          } else {
              sidebar.style.left = '0px';
          }
          var openbtn = document.getElementById("openbtn");
          if (openbtn.style.left === '382px') {
              openbtn.style.left = '-2px';
              openbtn.title = 'Show Sidebar';
          } else {
              openbtn.style.left = '382px';
              openbtn.title = 'Hide Sidebar';
          }
          var gfa_tab = document.getElementById("gfa_tab");
          if (gfa_tab.style.left === '407px') {
              gfa_tab.style.left = '-23px';
          } else {
              gfa_tab.style.left = '407px';
          }
          var rb_tab = document.getElementById("rb_tab");
          if (rb_tab.style.left === '407px') {
              rb_tab.style.left = '-23px';
          } else {
              rb_tab.style.left = '407px';
          }
          var icon = openbtn.querySelector('i');
          if (openbtn.style.left === '382px') {
              icon.classList.remove('fa-angle-right');
              icon.classList.add('fa-angle-left');
          } else {
              icon.classList.remove('fa-angle-left');
              icon.classList.add('fa-angle-right');
          }
        }
    
        function openTab(evt, tabName) {
            var gfaInfoBox = document.getElementById('GFAInfoBox');
            var rbInfoBox = document.getElementById('RBInfoBox');
    
            var gfaButton = document.querySelector('.gfa_tab');
            var rbButton = document.querySelector('.rb_tab');
    
            gfaInfoBox.style.display = 'none';
            rbInfoBox.style.display = 'none';
    
            gfaButton.classList.remove('active-tab');
            rbButton.classList.remove('active-tab');
    
            if (tabName === 'gfa_tab') {
                gfaInfoBox.style.display = 'block';
                gfaButton.classList.add('active-tab');
    
                // Show GFA layers and hide RB layers
                rbLayers.forEach(layer => {
                    if (map.hasLayer(layer)) {
                        map.removeLayer(layer);
                    }
                });
                gfaLayers.forEach(layer => {
                    if (!map.hasLayer(layer)) {
                        map.addLayer(layer);
                    }
                });
    
            } else if (tabName === 'rb_tab') {
                rbInfoBox.style.display = 'block';
                rbButton.classList.add('active-tab');
    
                // Show RB layers and hide GFA layers
                gfaLayers.forEach(layer => {
                    if (map.hasLayer(layer)) {
                        map.removeLayer(layer);
                    }
                });
                rbLayers.forEach(layer => {
                    if (!map.hasLayer(layer)) {
                        map.addLayer(layer);
                    }
                });
            }
        }
    
        // Set up the page on load
        window.addEventListener('load', function() {
            initializeMapAndLayers();
            
            var gfaButton = document.getElementById('gfa_tab');
            var rbButton = document.getElementById('rb_tab');
            var gfaInfoBox = document.getElementById('GFAInfoBox');
            var rbInfoBox = document.getElementById('RBInfoBox');
    
            // Set GFA as active tab and visible info box
            gfaButton.classList.add('active-tab');
            gfaInfoBox.style.display = 'block';
            
            // Ensure the other tab and info box are in the inactive state
            rbButton.classList.remove('active-tab');
            rbInfoBox.style.display = 'none';
        });
        document.addEventListener("DOMContentLoaded", function() {
            var layerControlToggle = document.querySelector('.leaflet-control-layers-toggle');
            if (layerControlToggle) {
                layerControlToggle.click();
            }
        });
    </script>
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            soup = BeautifulSoup(content, 'html.parser')

        # Insert sidebar HTML right after the opening body tag
        body = soup.find('body')
        if body:
            sidebar_html_soup = BeautifulSoup(sidebar_html, 'html.parser')
            body.insert(0, sidebar_html_soup.div)
            body.insert(1, sidebar_html_soup.button)

        # Find the head tag to insert CSS and JS
        head = soup.find('head')
        if head:
            head.append(BeautifulSoup(sidebar_css, 'html.parser'))
            body.append(BeautifulSoup(sidebar_js, 'html.parser'))

        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(str(soup))
            
    except FileNotFoundError:
        print(f"Error: The file {file_path} was not found.")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

# 5. Screenshot and Automation
# -----------------------------------------------------------------------------
# In your flood.py script, find the take_map_screenshot function.
def take_map_screenshot(html_file_path, output_image_path):
    print(f"Attempting to take screenshot of {html_file_path}...")
    try:
        # Set up Chrome options for a headless browser
        chrome_options = Options()
        chrome_options.add_argument("--headless")
        chrome_options.add_argument("--no-sandbox")
        chrome_options.add_argument("--disable-dev-shm-usage")
        chrome_options.add_argument("--window-size=988,1227")
        chrome_options.add_argument("--hide-scrollbars")
        chrome_options.add_argument("--force-device-scale-factor=1")

        # Let Selenium find the chromedriver from the system PATH
        # The browser-actions/setup-chrome action handles placing it there
        service = Service()
        driver = webdriver.Chrome(service=service, options=chrome_options)

        # Load the HTML file from the local file system
        full_path = 'file://' + os.path.abspath(html_file_path)
        driver.get(full_path)

        # Wait for the map to fully load
        WebDriverWait(driver, 30).until(
            EC.presence_of_element_located((By.CLASS_NAME, "leaflet-container"))
        )
        time.sleep(3)

        map_id = driver.execute_script("""
            var mapElement = document.querySelector('.leaflet-container');
            if (mapElement && mapElement.id) {
                return mapElement.id;
            }
            return null;
        """)

        if map_id:
            driver.execute_script(f"{map_id}.panBy([-190, 10]);")
            time.sleep(1) # Give map time to complete pan animation

            print("Attempting to hide '18 Major River Basins' layer...")
            try:
                # 2. Wait for the layer control to become expanded/visible
                WebDriverWait(driver, 10).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, '.leaflet-control-layers.leaflet-control-layers-expanded'))
                )
                print("Layer control is expanded.")
                time.sleep(0.5) # Small delay after expansion for elements to fully render

                # --- NEW STRATEGY START ---
                # 3. Find all overlay checkboxes and iterate to find the correct one
                print("Searching for the '18 Major River Basins' checkbox by iterating through all layer options...")
                all_overlay_checkboxes = WebDriverWait(driver, 10).until(
                    EC.presence_of_all_elements_located((By.CSS_SELECTOR, '.leaflet-control-layers-overlays input[type="checkbox"]'))
                )
                
                target_checkbox = None
                for checkbox in all_overlay_checkboxes:
                    # Get the text content of the parent label using JavaScript for robustness
                    label_text = driver.execute_script("return arguments[0].parentNode.textContent;", checkbox)
                    if "18 Major River Basins" in label_text:
                        target_checkbox = checkbox
                        break # Found the correct checkbox, exit loop
                
                if target_checkbox:
                    print("Found '18 Major River Basins' checkbox.")
                    if target_checkbox.is_selected():
                        print("18 Major River Basins layer is currently visible. Clicking to hide...")
                        target_checkbox.click()
                        time.sleep(1) # Give map time to re-render after layer change
                        print("Layer hidden.")
                    else:
                        print("18 Major River Basins layer is already hidden.")
                else:
                    print("ERROR: Could not find '18 Major River Basins' checkbox by iterating. "
                          "Please ensure the layer name is exactly as displayed or check the HTML structure if it's very unusual.")

                # --- NEW CODE ADDITION START ---
                # Collapse the layer control by simulating a mouseout event
                print("Collapsing layer control by simulating mouseout...")
                
                # Find the main layer control container, which should currently be expanded.
                # We reuse the CSS selector used before to confirm it's expanded.
                layer_control_container = WebDriverWait(driver, 5).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, '.leaflet-control-layers.leaflet-control-layers-expanded'))
                )
                
                # Execute JavaScript to dispatch a mouseout event on this container element.
                # This simulates the mouse leaving the area of the control.
                driver.execute_script("""
                    var element = arguments[0]; // Get the element passed from Python
                    var event = new MouseEvent('mouseout', {
                        'view': window,
                        'bubbles': true,    // The event will bubble up the DOM tree
                        'cancelable': true  // The default action of the event can be prevented
                    });
                    element.dispatchEvent(event);
                """, layer_control_container) # Pass the Selenium WebElement to the JavaScript context

                time.sleep(0.5) # Give a small delay for the control to visually collapse
                print("Layer control collapsed.")
                # --- NEW CODE ADDITION END ---

            except Exception as e:
                print(f"An unexpected error occurred while interacting with the layer control: {e}")
                traceback.print_exc()
            
            driver.save_screenshot(output_image_path)
            print(f"Screenshot saved to {output_image_path}.")
        else:
            print("Could not find the map container ID. Cannot pan or hide layers.")

    except Exception as e:
        print(f"An error occurred during screenshot capture: {e}")
        traceback.print_exc()
    finally:
        driver.quit()
        print("WebDriver closed.")
        
# 6. Main Execution Block
# -----------------------------------------------------------------------------
if __name__ == "__main__":
    current_time = datetime.now(pytz.timezone('Asia/Manila'))
    current_date = current_time.date()

    if current_time.hour < 6:
        user_date_input = (current_date - timedelta(days=1)).strftime('%Y-%m-%d')
        user_am_pm_input = 'pm'
        print(f"Current time is before 6:00 AM. Setting date to {user_date_input} and time to PM.")
    elif 6 <= current_time.hour < 18:
        user_date_input = current_date.strftime('%Y-%m-%d')
        user_am_pm_input = 'am'
        print(f"Current time is between 6:00 AM and 6:00 PM. Setting date to {user_date_input} and time to AM.")
    else:
        user_date_input = current_date.strftime('%Y-%m-%d')
        user_am_pm_input = 'pm'
        print(f"Current time is after 6:00 PM. Setting date to {user_date_input} and time to PM.")

    start_time = time.perf_counter()

    gfa_identifiers = extract_gfa_identifiers(user_date_input, user_am_pm_input)
    
    # gfa_identifiers = ['d9f8c9db-e913-4220-a554-c1faae84abef', '9246961f-2e50-433d-a083-1fcb6fec3207', '09d04c75-3292-4dd9-85b9-52481d79d72f', '425d9a82-a60b-4e55-a02d-c83900baa33b', '1cadd0b0-b5bc-421e-bca2-7dc9708fda6a', '8918a4f2-8046-446e-ab4f-9c378bc89f4f', '4409e18f-4258-4110-aad9-b37ab8221e14', 'e2830f08-be4f-417c-af52-9a18ce347f78', 'd60b4c63-9f5f-4bd4-920b-1392a2da9d9f', 'e00a559f-c78f-4fff-ac01-12d8c52b27f5']

    if gfa_identifiers:
        all_raw_gfa_cap_data = {}
        for identifier in gfa_identifiers:
            print(f"Downloading and parsing CAP file: {identifier}")
            cap_data = extract_cap_data(identifier)
            if cap_data:
                all_raw_gfa_cap_data[identifier] = cap_data

        if all_raw_gfa_cap_data:
            print("\nFiltering advisories to remove cancellations...")
            filtered_gfa_data_for_map = filter_active_advisories(all_raw_gfa_cap_data)

            if filtered_gfa_data_for_map:
                map_output_path = "flood.html"
                m = create_flood_map(filtered_gfa_data_for_map, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
                m.save(map_output_path)
                inject_sidebar_html(map_output_path, filtered_gfa_data_for_map, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
                screenshot_output_path = "gfamap_new.png"
                take_map_screenshot(map_output_path, screenshot_output_path)
            else:
                print("After filtering, no active General Flood Advisory data remains for mapping.")
                map_output_path = "flood.html"
                m = create_flood_map({}, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
                m.save(map_output_path)
                inject_sidebar_html(map_output_path, {}, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
                screenshot_output_path = "gfamap_new.png"
                take_map_screenshot(map_output_path, screenshot_output_path)
        else:
            print("No CAP data could be extracted for the specified General Flood Advisory identifiers (even before filtering).")
            map_output_path = "flood.html"
            m = create_flood_map({}, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
            m.save(map_output_path)
            inject_sidebar_html(map_output_path, {}, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
            screenshot_output_path = "gfamap_new.png"
            take_map_screenshot(map_output_path, screenshot_output_path)
    else:
        print("No General Flood Advisory identifiers found matching your criteria.")
        map_output_path = "flood.html"
        m = create_flood_map({}, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
        m.save(map_output_path)
        inject_sidebar_html(map_output_path, {}, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
        screenshot_output_path = "gfamap_new.png"
        take_map_screenshot(map_output_path, screenshot_output_path)

    end_time = time.perf_counter()
    duration = end_time - start_time
    minutes = int(duration // 60)
    seconds = duration % 60

    print(f"\nProcess completed in {duration:.0f} seconds.")


