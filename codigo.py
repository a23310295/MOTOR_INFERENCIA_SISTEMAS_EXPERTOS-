#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
================================================================================
  ANALIZADOR DE LÓGICA PROPOSICIONAL POR TABLEAUX SEMÁNTICOS
  Implementado con Procesamiento de Lenguaje Natural en Español
================================================================================
  Autor   : Senior Python Developer / AI Expert (Sistemas Expertos)
  Versión : 3.0 (Persistencia automática al salir, guardado de casos con nombre,
            historial de textos, selector dinámico y gestión de archivos)
================================================================================
"""

import tkinter as tk
from tkinter import ttk, messagebox, font, simpledialog
import re
import os
import json
import math
from dataclasses import dataclass, field
from typing import Optional, List, Tuple, Dict
from copy import deepcopy

# ─────────────────────────────────────────────────────────────────────────────
#  MÓDULO 1: REPRESENTACIÓN DE FÓRMULAS LÓGICAS
# ─────────────────────────────────────────────────────────────────────────────

class Formula:
    """
    Representa una Fórmula Bien Formada (WFF) de la Lógica Proposicional.
    Almacena la fórmula como un árbol de sintaxis abstracta (AST).

    Tipos de nodo:
      - 'atom'  : Literal proposicional (p, q, r, ...)
      - 'neg'   : Negación ¬A
      - 'and'   : Conjunción A ∧ B
      - 'or'    : Disyunción A ∨ B
      - 'impl'  : Condicional / Implicación A → B
      - 'bimp'  : Bicondicional / Doble Implicación A ↔ B
    """

    SYMBOLS = {
        'neg': '¬', 'and': '∧', 'or': '∨',
        'impl': '→', 'bimp': '↔'
    }

    CONNECTOR_NAMES = {
        'atom': 'Átomo (Proposición simple)',
        'neg':  'Negación (¬)',
        'and':  'Conjunción (∧)',
        'or':   'Disyunción (∨)',
        'impl': 'Condicional / Implicación (→)',
        'bimp': 'Bicondicional (↔)'
    }

    def __init__(self, kind: str, name: str = '',
                 left: 'Formula' = None, right: 'Formula' = None):
        self.kind  = kind    # Tipo de nodo
        self.name  = name    # Nombre del átomo (si kind == 'atom')
        self.left  = left    # Sub-fórmula izquierda
        self.right = right   # Sub-fórmula derecha

    # ── Constructores estáticos de conveniencia ──────────────────────────────

    @staticmethod
    def atom(name: str) -> 'Formula':
        return Formula('atom', name=name)

    @staticmethod
    def neg(f: 'Formula') -> 'Formula':
        return Formula('neg', left=f)

    @staticmethod
    def and_(l: 'Formula', r: 'Formula') -> 'Formula':
        return Formula('and', left=l, right=r)

    @staticmethod
    def or_(l: 'Formula', r: 'Formula') -> 'Formula':
        return Formula('or', left=l, right=r)

    @staticmethod
    def impl(l: 'Formula', r: 'Formula') -> 'Formula':
        return Formula('impl', left=l, right=r)

    @staticmethod
    def bimp(l: 'Formula', r: 'Formula') -> 'Formula':
        return Formula('bimp', left=l, right=r)

    def connector_description(self) -> str:
        """Devuelve el nombre legible en español del conector principal."""
        if self.kind == 'neg':
            if self.left and self.left.kind != 'atom':
                return f"Negación de {self.left.connector_description().split(' ')[0]}"
            return 'Negación (¬)'
        return self.CONNECTOR_NAMES.get(self.kind, 'Desconocido')

    # ── Representación en cadena ─────────────────────────────────────────────

    def __str__(self) -> str:
        if self.kind == 'atom':
            return self.name
        if self.kind == 'neg':
            inner = str(self.left)
            if self.left.kind == 'atom':
                return f'¬{inner}'
            return f'¬({inner})'
        sym = self.SYMBOLS[self.kind]
        ls = str(self.left)
        rs = str(self.right)
        if self.left.kind not in ('atom', 'neg'):
            ls = f'({ls})'
        if self.right.kind not in ('atom', 'neg'):
            rs = f'({rs})'
        return f'{ls} {sym} {rs}'

    def __eq__(self, other) -> bool:
        if not isinstance(other, Formula):
            return False
        return str(self) == str(other)

    def __hash__(self):
        return hash(str(self))

    def clone(self) -> 'Formula':
        """Copia profunda de la fórmula."""
        return deepcopy(self)

    def atoms(self) -> set:
        """Retorna el conjunto de nombres de átomos en la fórmula."""
        if self.kind == 'atom':
            return {self.name}
        result = set()
        if self.left:
            result |= self.left.atoms()
        if self.right:
            result |= self.right.atoms()
        return result


# ─────────────────────────────────────────────────────────────────────────────
#  MÓDULO 2: PARSER DE LENGUAJE NATURAL EN ESPAÑOL
# ─────────────────────────────────────────────────────────────────────────────

class NLPParser:
    """
    Convierte oraciones en español a Fórmulas Bien Formadas (WFF).

    Estrategia de análisis:
      1. Detectar el conectivo principal de mayor alcance.
      2. Normalizar texto (minúsculas, sin puntuación irrelevante).
      3. Mapear proposiciones simples a letras proposicionales.
      4. Reutilizar la misma letra cuando la misma idea se repite.
    """

    def __init__(self):
        self._prop_map: Dict[str, str] = {}
        self.atom_descriptions: Dict[str, str] = {}
        self._letter_index = 0

    def _next_letter(self) -> str:
        """Genera la siguiente letra proposicional disponible."""
        letters = list('pqrstuvwxyz')
        if self._letter_index < len(letters):
            l = letters[self._letter_index]
        else:
            l = f'p{self._letter_index - len(letters) + 2}'
        self._letter_index += 1
        return l

    def _normalize(self, text: str) -> str:
        """Normaliza texto: minúsculas, sin puntuación, sin espacios extra."""
        text = text.lower().strip()
        text = re.sub(r'[",;:.!?¡¿]', '', text)
        text = re.sub(r'\s+', ' ', text)
        return text.strip()

    def _get_or_create_atom(self, text: str) -> Tuple[str, bool]:
        """
        Obtiene o crea la letra proposicional para una proposición simple.
        Detecta si hay negación y la separa del núcleo proposicional.
        """
        text = self._normalize(text)

        negated = False
        neg_match = re.match(
            r'^(no|jamás|nunca)\s+(.+)$', text, re.IGNORECASE
        )
        if neg_match:
            negated = True
            text = neg_match.group(2).strip()

        text = re.sub(r'^ni\s+', '', text).strip()

        if text in self._prop_map:
            letter = self._prop_map[text]
            return letter, negated

        letter = self._next_letter()
        self._prop_map[text] = letter
        self.atom_descriptions[letter] = text
        return letter, negated

    def _text_to_formula(self, text: str) -> Optional[Formula]:
        """Convierte recursivamente un fragmento de texto en una Formula."""
        text = self._normalize(text)
        if not text:
            return None

        # ── Bicondicional: "si y solo si" ────────────────────────────────────
        bimp_match = re.search(r'\bsi y s[oó]lo si\b', text, re.IGNORECASE)
        if bimp_match:
            left_txt  = text[:bimp_match.start()].strip()
            right_txt = text[bimp_match.end():].strip()
            left_f  = self._text_to_formula(left_txt)
            right_f = self._text_to_formula(right_txt)
            if left_f and right_f:
                return Formula.bimp(left_f, right_f)

        # ── Implicación: "si ... entonces ..." ───────────────────────────────
        impl_match = re.match(
            r'^si\s+(.+?)\s+entonces\s+(.+)$', text, re.IGNORECASE
        )
        if impl_match:
            antecedent = impl_match.group(1).strip()
            consequent = impl_match.group(2).strip()
            left_f  = self._text_to_formula(antecedent)
            right_f = self._text_to_formula(consequent)
            if left_f and right_f:
                return Formula.impl(left_f, right_f)

        # ── Implicación alternativa: "implica", "por lo tanto" ───────────────
        for trigger in [r'\bimplica\b', r'\bpor lo tanto\b', r'\bpor tanto\b']:
            m = re.search(trigger, text, re.IGNORECASE)
            if m:
                left_txt  = text[:m.start()].strip()
                right_txt = text[m.end():].strip()
                left_f  = self._text_to_formula(left_txt)
                right_f = self._text_to_formula(right_txt)
                if left_f and right_f:
                    return Formula.impl(left_f, right_f)

        # ── Conjunción: " y " ────────────────────────────────────────────────
        and_parts = self._split_by_connective(
            text, r'\s+y\s+(?!s[oó]lo si)', 'and'
        )
        if and_parts:
            formulas = [self._text_to_formula(p) for p in and_parts]
            formulas = [f for f in formulas if f]
            if len(formulas) >= 2:
                result = formulas[0]
                for f in formulas[1:]:
                    result = Formula.and_(result, f)
                return result

        # ── Disyunción: " o " ────────────────────────────────────────────────
        or_parts = self._split_by_connective(text, r'\s+[ou]\s+', 'or')
        if or_parts:
            formulas = [self._text_to_formula(p) for p in or_parts]
            formulas = [f for f in formulas if f]
            if len(formulas) >= 2:
                result = formulas[0]
                for f in formulas[1:]:
                    result = Formula.or_(result, f)
                return result

        # ── Proposición simple (con posible negación) ─────────────────────────
        letter, negated = self._get_or_create_atom(text)
        f = Formula.atom(letter)
        if negated:
            f = Formula.neg(f)
        return f

    def _split_by_connective(self, text: str, pattern: str,
                              kind: str) -> Optional[List[str]]:
        parts = re.split(pattern, text, flags=re.IGNORECASE)
        if len(parts) >= 2 and all(p.strip() for p in parts):
            return [p.strip() for p in parts]
        return None

    def parse_knowledge_base(self, raw_text: str) -> List[Tuple[str, Formula]]:
        self.__init__()
        sentences = []
        lines = [l.strip() for l in raw_text.split('\n') if l.strip()]
        for line in lines:
            sub = re.split(r'\.\s*', line)
            for s in sub:
                s = s.strip().strip('"\'').strip()
                if s:
                    sentences.append(s)

        results = []
        for sentence in sentences:
            formula = self._text_to_formula(sentence)
            if formula:
                results.append((sentence, formula))

        return results


# ─────────────────────────────────────────────────────────────────────────────
#  MÓDULO 3: NODO Y RAMA DEL TABLEAU CON SOPORTE PARA ÁRBOL JERÁRQUICO
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class TableauNode:
    formula:   Formula
    processed: bool = False
    source:    str  = ''

    def __str__(self):
        tick = '✓' if self.processed else ' '
        return f'[{tick}] {self.formula}'


class TableauBranch:
    _id_counter = 0

    def __init__(self, nodes: List[TableauNode] = None, parent: Optional['TableauBranch'] = None):
        TableauBranch._id_counter += 1
        self.id = TableauBranch._id_counter
        self.nodes = list(nodes) if nodes else []
        self.closed = False
        self.parent = parent
        self.parent_id = parent.id if parent else -1
        self.close_reason = ''
        self.children: List['TableauBranch'] = []
        self.step_added_formulas: List[Formula] = []
        self.branch_label: str = ''

    def add(self, formula: Formula, source: str = '') -> 'TableauBranch':
        if not any(str(n.formula) == str(formula) for n in self.nodes):
            self.nodes.append(TableauNode(formula=formula, source=source))
            self.step_added_formulas.append(formula)
        return self

    def literals(self) -> Dict[str, bool]:
        result = {}
        for node in self.nodes:
            f = node.formula
            if f.kind == 'atom':
                result[f.name] = True
            elif f.kind == 'neg' and f.left.kind == 'atom':
                result[f.left.name] = False
        return result

    def check_closed(self) -> bool:
        pos_atoms = {
            node.formula.name
            for node in self.nodes
            if node.formula.kind == 'atom'
        }
        neg_atoms = {
            node.formula.left.name
            for node in self.nodes
            if node.formula.kind == 'neg' and node.formula.left.kind == 'atom'
        }
        intersection = pos_atoms & neg_atoms
        if intersection:
            atom = next(iter(intersection))
            self.closed = True
            self.close_reason = f'{atom} y ¬{atom}'
            return True
        return False

    def next_unprocessed(self) -> Optional[TableauNode]:
        for node in self.nodes:
            if not node.processed and not self._is_literal(node.formula):
                return node
        return None

    @staticmethod
    def _is_literal(f: Formula) -> bool:
        return (f.kind == 'atom' or
                (f.kind == 'neg' and f.left.kind == 'atom'))

    def is_complete(self) -> bool:
        if self.closed:
            return True
        return self.next_unprocessed() is None

    def clone_nodes(self) -> List[TableauNode]:
        return [TableauNode(
            formula=n.formula.clone(),
            processed=n.processed,
            source=n.source
        ) for n in self.nodes]

    def model(self, all_atoms: set) -> Dict[str, bool]:
        lits = self.literals()
        m = {}
        for atom in sorted(all_atoms):
            m[atom] = lits.get(atom, False)
        return m


# ─────────────────────────────────────────────────────────────────────────────
#  MÓDULO 4: MOTOR DE TABLEAUX SEMÁNTICOS
# ─────────────────────────────────────────────────────────────────────────────

class TableauxEngine:
    def __init__(self):
        self.root: Optional[TableauBranch] = None
        self.active_branches: List[TableauBranch] = []
        self.all_created_branches: List[TableauBranch] = []
        self.steps: List[dict] = []
        self.all_atoms: set = set()

    def initialize(self, formulas: List[Formula]):
        TableauBranch._id_counter = 0
        root = TableauBranch()
        root.branch_label = "Raíz (Premisas)"
        for f in formulas:
            root.add(f, source='KB')
            self.all_atoms |= f.atoms()

        root.check_closed()
        self.root = root
        self.active_branches = [root]
        self.all_created_branches = [root]

    def expand(self) -> bool:
        for branch in self.active_branches:
            if branch.closed or branch.is_complete():
                continue

            node = branch.next_unprocessed()
            if node is None:
                continue

            node.processed = True
            f = node.formula

            # Doble Negación: ¬¬A → A (Regla Alfa)
            if f.kind == 'neg' and f.left.kind == 'neg':
                inner = f.left.left.clone()
                branch.add(inner, source='¬¬ elim')
                self.steps.append({
                    'rule': 'Alfa (Lineal)',
                    'rule_name': 'Eliminación de Doble Negación (¬¬A)',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(inner)],
                    'splits': False,
                    'explanation': f"Como se tiene ¬¬({inner}), por equivalencia de doble negación se deduce directamente que '{inner}' es verdadero en la misma rama (no ramifica)."
                })
                branch.check_closed()
                return True

            # Conjunción: A ∧ B → A, B (Regla Alfa)
            if f.kind == 'and':
                branch.add(f.left.clone(),  source='∧ elim L')
                branch.add(f.right.clone(), source='∧ elim R')
                self.steps.append({
                    'rule': 'Alfa (Lineal)',
                    'rule_name': 'Descomposición de Conjunción (A ∧ B)',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(f.left), str(f.right)],
                    'splits': False,
                    'explanation': f"Para que la conjunción '{f}' sea verdadera, deben ser verdaderos ambos términos. Por tanto, se añaden '{f.left}' y '{f.right}' a la misma rama sin ramificar."
                })
                branch.check_closed()
                return True

            # ¬(A ∨ B) → ¬A, ¬B (Regla Alfa)
            if f.kind == 'neg' and f.left.kind == 'or':
                na = Formula.neg(f.left.left.clone())
                nb = Formula.neg(f.left.right.clone())
                branch.add(na, source='¬∨ elim L')
                branch.add(nb, source='¬∨ elim R')
                self.steps.append({
                    'rule': 'Alfa (Lineal)',
                    'rule_name': 'Negación de Disyunción ¬(A ∨ B) [De Morgan]',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(na), str(nb)],
                    'splits': False,
                    'explanation': f"Negar una disyunción ¬({f.left}) exige que ambas opciones sean falsas. Por Ley de De Morgan se agregan simultáneamente '{na}' y '{nb}' a la misma rama."
                })
                branch.check_closed()
                return True

            # ¬(A → B) → A, ¬B (Regla Alfa)
            if f.kind == 'neg' and f.left.kind == 'impl':
                a  = f.left.left.clone()
                nb = Formula.neg(f.left.right.clone())
                branch.add(a,  source='¬→ elim antec')
                branch.add(nb, source='¬→ elim cons')
                self.steps.append({
                    'rule': 'Alfa (Lineal)',
                    'rule_name': 'Negación de Condicional ¬(A → B)',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(a), str(nb)],
                    'splits': False,
                    'explanation': f"Un condicional sólo es falso cuando el antecedente es verdadero y el consecuente falso. De ¬({f.left}) se infiere que '{a}' es V y '{nb}' es V."
                })
                branch.check_closed()
                return True

            # Disyunción: A ∨ B (Regla Beta)
            if f.kind == 'or':
                left_branch, right_branch = self._split_branch(
                    branch,
                    f.left.clone(),
                    f.right.clone(),
                    '∨ izq', '∨ der',
                    label_left=f"{f.left}",
                    label_right=f"{f.right}"
                )
                self.steps.append({
                    'rule': 'Beta (Ramificada)',
                    'rule_name': 'Bifurcación de Disyunción (A ∨ B)',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(f.left), str(f.right)],
                    'splits': True,
                    'children': [left_branch.id, right_branch.id],
                    'explanation': f"La disyunción '{f}' se cumple si al menos uno es verdadero. Se abren dos alternativas independientes: el camino izquierdo con '{f.left}' y el derecho con '{f.right}'."
                })
                return True

            # Implicación: A → B (Regla Beta)
            if f.kind == 'impl':
                na = Formula.neg(f.left.clone())
                b  = f.right.clone()
                left_branch, right_branch = self._split_branch(
                    branch, na, b,
                    '→ izq', '→ der',
                    label_left=f"¬{f.left}",
                    label_right=f"{b}"
                )
                self.steps.append({
                    'rule': 'Beta (Ramificada)',
                    'rule_name': 'Bifurcación de Implicación (A → B)',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(na), str(b)],
                    'splits': True,
                    'children': [left_branch.id, right_branch.id],
                    'explanation': f"Por equivalencia material, '{f}' equivale a ¬({f.left}) ∨ {b}. Por lo tanto, el árbol se ramifica en dos caminos: o bien el antecedente es falso ('{na}') o bien el consecuente es verdadero ('{b}')."
                })
                return True

            # ¬(A ∧ B) (Regla Beta)
            if f.kind == 'neg' and f.left.kind == 'and':
                na = Formula.neg(f.left.left.clone())
                nb = Formula.neg(f.left.right.clone())
                left_branch, right_branch = self._split_branch(
                    branch, na, nb,
                    '¬∧ izq', '¬∧ der',
                    label_left=f"{na}",
                    label_right=f"{nb}"
                )
                self.steps.append({
                    'rule': 'Beta (Ramificada)',
                    'rule_name': 'Negación de Conjunción ¬(A ∧ B) [De Morgan]',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(na), str(nb)],
                    'splits': True,
                    'children': [left_branch.id, right_branch.id],
                    'explanation': f"Para que la conjunción sea falsa, al menos uno de sus miembros debe fallar. Se abren dos ramas: una donde falla el primero ('{na}') y otra donde falla el segundo ('{nb}')."
                })
                return True

            # Bicondicional: A ↔ B (Regla Beta)
            if f.kind == 'bimp':
                ab   = Formula.and_(f.left.clone(), f.right.clone())
                nanb = Formula.and_(
                    Formula.neg(f.left.clone()),
                    Formula.neg(f.right.clone())
                )
                left_branch, right_branch = self._split_branch(
                    branch, ab, nanb,
                    '↔ izq', '↔ der',
                    label_left=f"{f.left} ∧ {f.right}",
                    label_right=f"¬{f.left} ∧ ¬{f.right}"
                )
                self.steps.append({
                    'rule': 'Beta (Ramificada)',
                    'rule_name': 'Bifurcación de Bicondicional (A ↔ B)',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(ab), str(nanb)],
                    'splits': True,
                    'children': [left_branch.id, right_branch.id],
                    'explanation': f"El bicondicional '{f}' es verdadero si ambos tienen el mismo valor de verdad. Se bifurca en: camino 1 (ambos verdaderos: '{ab}') y camino 2 (ambos falsos: '{nanb}')."
                })
                return True

            # ¬(A ↔ B) (Regla Beta)
            if f.kind == 'neg' and f.left.kind == 'bimp':
                anb  = Formula.and_(
                    f.left.left.clone(),
                    Formula.neg(f.left.right.clone())
                )
                nab  = Formula.and_(
                    Formula.neg(f.left.left.clone()),
                    f.left.right.clone()
                )
                left_branch, right_branch = self._split_branch(
                    branch, anb, nab,
                    '¬↔ izq', '¬↔ der',
                    label_left=f"{f.left.left} ∧ ¬{f.left.right}",
                    label_right=f"¬{f.left.left} ∧ {f.left.right}"
                )
                self.steps.append({
                    'rule': 'Beta (Ramificada)',
                    'rule_name': 'Negación de Bicondicional ¬(A ↔ B)',
                    'from': str(f),
                    'branch': branch.id,
                    'adds': [str(anb), str(nab)],
                    'splits': True,
                    'children': [left_branch.id, right_branch.id],
                    'explanation': f"Un bicondicional es falso cuando sus valores difieren. Se ramifica en: '{anb}' (primero V, segundo F) o '{nab}' (primero F, segundo V)."
                })
                return True

        return False

    def _split_branch(
        self, parent: TableauBranch,
        left_formula: Formula, right_formula: Formula,
        left_src: str, right_src: str,
        label_left: str = '', label_right: str = ''
    ) -> Tuple[TableauBranch, TableauBranch]:
        left_branch = TableauBranch(
            nodes=parent.clone_nodes(),
            parent=parent
        )
        left_branch.branch_label = label_left or str(left_formula)
        left_branch.add(left_formula, source=left_src)
        left_branch.check_closed()

        right_branch = TableauBranch(
            nodes=parent.clone_nodes(),
            parent=parent
        )
        right_branch.branch_label = label_right or str(right_formula)
        right_branch.add(right_formula, source=right_src)
        right_branch.check_closed()

        parent.children = [left_branch, right_branch]
        self.all_created_branches.extend([left_branch, right_branch])

        idx = self.active_branches.index(parent)
        self.active_branches[idx:idx+1] = [left_branch, right_branch]

        return left_branch, right_branch

    def run(self, max_steps: int = 200) -> bool:
        changed = True
        step_count = 0
        while changed and step_count < max_steps:
            changed = self.expand()
            step_count += 1
        return step_count > 0

    @property
    def branches(self) -> List[TableauBranch]:
        return self.active_branches

    def open_branches(self) -> List[TableauBranch]:
        return [b for b in self.active_branches if not b.closed]

    def is_unsatisfiable(self) -> bool:
        return all(b.closed for b in self.active_branches)

    def models(self) -> List[Dict[str, bool]]:
        return [b.model(self.all_atoms) for b in self.open_branches()]


# ─────────────────────────────────────────────────────────────────────────────
#  MÓDULO 5: INTERFAZ GRÁFICA (GUI) CON PERSISTENCIA Y SELECCIÓN DE TEXTOS
# ─────────────────────────────────────────────────────────────────────────────

COLORS = {
    'bg_main':      '#1E1E2E',
    'bg_panel':     '#2A2A3E',
    'bg_input':     '#13131F',
    'bg_tree':      '#161625',
    'node_bg':      '#24273A',
    'node_border':  '#494D64',
    'accent':       '#7C3AED',
    'accent_light': '#A855F7',
    'success':      '#10B981',
    'danger':       '#EF4444',
    'warning':      '#F59E0B',
    'info':         '#38BDF8',
    'text_main':    '#E2E8F0',
    'text_dim':     '#94A3B8',
    'text_code':    '#A5F3FC',
    'border':       '#374151',
    'btn_bg':       '#7C3AED',
    'btn_hover':    '#6D28D9',
    'btn_text':     '#FFFFFF',
}

# Archivo de guardado automático
SAVE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tableaux_saved_data.json')

PRESET_EXAMPLES = {
    'Caso Prueba (Implicación + Negación)': (
        'Si es de día, entonces voy a trabajar\n'
        'Si llueve, entonces no voy a trabajar\n'
        'Es de día'
    ),
    'Contradicción Directa': 'Hace sol y no hace sol',
    'Disyunción (O)': 'Juan estudia o María trabaja\nJuan no estudia',
    'Bicondicional (Si y solo si)': 'Hay luz si y solo si hay electricidad\nHay electricidad',
    'Regla Alfa (Conjunción Y)': 'Está nublado y hace frío\nSi hace frío, entonces llevo abrigo'
}


class TableauxGUI:
    """
    Interfaz Gráfica del Analizador con Persistencia de Sesión y Gestor de Casos.
    """

    def __init__(self, root: tk.Tk):
        self.root = root
        self.saved_cases: Dict[str, str] = {}
        self.last_text: str = ''
        self._load_storage()

        self._configure_root()
        self._define_fonts()
        self._define_styles()
        self._build_ui()

        # Vincular evento de cierre para auto-guardar
        self.root.protocol("WM_DELETE_WINDOW", self._on_close_window)

    def _configure_root(self):
        self.root.title('Analizador de Tableaux Semánticos — Lógica Proposicional')
        self.root.geometry('1380x880')
        self.root.minsize(950, 700)
        self.root.configure(bg=COLORS['bg_main'])

    def _define_fonts(self):
        self.font_title   = font.Font(family='Segoe UI', size=16, weight='bold')
        self.font_header  = font.Font(family='Segoe UI', size=11, weight='bold')
        self.font_body    = font.Font(family='Segoe UI', size=10)
        self.font_code    = font.Font(family='Consolas', size=11)
        self.font_code_sm = font.Font(family='Consolas', size=9)
        self.font_result  = font.Font(family='Consolas', size=12, weight='bold')

    def _define_styles(self):
        style = ttk.Style(self.root)
        style.theme_use('clam')

        style.configure('.',
            background=COLORS['bg_panel'],
            foreground=COLORS['text_main'],
            bordercolor=COLORS['border'],
            troughcolor=COLORS['bg_main'],
            selectbackground=COLORS['accent'],
            selectforeground='white'
        )

        style.configure('Tableau.Treeview',
            background=COLORS['bg_tree'],
            foreground=COLORS['text_main'],
            fieldbackground=COLORS['bg_tree'],
            rowheight=28,
            font=('Consolas', 10)
        )
        style.configure('Tableau.Treeview.Heading',
            background=COLORS['accent'],
            foreground='white',
            font=('Segoe UI', 10, 'bold'),
            relief='flat'
        )
        style.map('Tableau.Treeview',
            background=[('selected', COLORS['accent_light'])],
            foreground=[('selected', 'white')]
        )

        style.configure('TNotebook',
            background=COLORS['bg_main'],
            tabmargins=[2, 5, 2, 0]
        )
        style.configure('TNotebook.Tab',
            background=COLORS['bg_panel'],
            foreground=COLORS['text_dim'],
            padding=[14, 6],
            font=('Segoe UI', 10, 'bold')
        )
        style.map('TNotebook.Tab',
            background=[('selected', COLORS['accent'])],
            foreground=[('selected', 'white')]
        )

        style.configure('TScrollbar',
            background=COLORS['bg_panel'],
            troughcolor=COLORS['bg_main'],
            arrowcolor=COLORS['text_dim']
        )
        style.configure('TSeparator', background=COLORS['border'])

        # Estilo para Combobox
        style.configure('TCombobox',
            fieldbackground=COLORS['bg_input'],
            background=COLORS['bg_panel'],
            foreground=COLORS['text_main'],
            arrowcolor=COLORS['accent_light']
        )

    # ── Manejo de Persistencia (Guardar / Cargar) ────────────────────────────

    def _load_storage(self):
        """Carga el estado guardado desde tableaux_saved_data.json."""
        self.saved_cases = dict(PRESET_EXAMPLES)
        self.last_text = PRESET_EXAMPLES['Caso Prueba (Implicación + Negación)']

        if os.path.exists(SAVE_FILE):
            try:
                with open(SAVE_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    user_cases = data.get('cases', {})
                    self.saved_cases.update(user_cases)
                    saved_last = data.get('last_text', '')
                    if saved_last.strip():
                        self.last_text = saved_last
            except Exception as e:
                print(f"Aviso: No se pudo cargar archivo de guardado ({e})")

    def _save_storage(self):
        """Guarda permanentemente los casos y el texto activo."""
        try:
            current_txt = self.input_text.get('1.0', 'end').strip()
            # Guardamos los casos que no sean los presets o si fueron editados
            data_to_save = {
                'last_text': current_txt,
                'cases': self.saved_cases
            }
            with open(SAVE_FILE, 'w', encoding='utf-8') as f:
                json.dump(data_to_save, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"Aviso: Error al auto-guardar datos ({e})")

    def _on_close_window(self):
        """Al cerrar la ventana se guarda el estado actual automáticamente."""
        self._save_storage()
        self.root.destroy()

    # ── Construcción de la UI ─────────────────────────────────────────────────

    def _build_ui(self):
        self._build_header()
        self._build_main_layout()

    def _build_header(self):
        header = tk.Frame(self.root, bg=COLORS['accent'], height=56)
        header.pack(fill='x', side='top')
        header.pack_propagate(False)

        tk.Label(
            header,
            text='🌳  Analizador de Tableaux Semánticos (Árboles de Refutación)',
            font=self.font_title,
            bg=COLORS['accent'],
            fg='white',
            padx=20
        ).pack(side='left', pady=10)

        status_lbl = tk.Label(
            header,
            text='💾 Auto-guardado activo  ·  Historial de Textos',
            font=self.font_body,
            bg=COLORS['accent'],
            fg='#DDD6FE',
            padx=14
        )
        status_lbl.pack(side='right', pady=16)

    def _build_main_layout(self):
        container = tk.Frame(self.root, bg=COLORS['bg_main'])
        container.pack(fill='both', expand=True, padx=10, pady=10)

        # Panel izquierdo (entrada)
        left_panel = tk.Frame(container, bg=COLORS['bg_panel'], width=380)
        left_panel.pack(side='left', fill='y', padx=(0, 8))
        left_panel.pack_propagate(False)
        self._build_input_panel(left_panel)

        # Panel derecho (resultados con tabs)
        right_panel = tk.Frame(container, bg=COLORS['bg_main'])
        right_panel.pack(side='left', fill='both', expand=True)
        self._build_results_panel(right_panel)

    def _build_input_panel(self, parent: tk.Frame):
        self._section_label(parent, '📁  Selector de Textos y Casos')

        # Selector desplegable de textos guardados / ejemplos
        sel_frame = tk.Frame(parent, bg=COLORS['bg_panel'])
        sel_frame.pack(fill='x', padx=10, pady=(4, 6))

        self.case_var = tk.StringVar()
        self.combo_cases = ttk.Combobox(
            sel_frame,
            textvariable=self.case_var,
            state='readonly',
            font=('Segoe UI', 9)
        )
        self._refresh_combobox_values()
        self.combo_cases.pack(side='left', fill='x', expand=True, padx=(0, 4))
        self.combo_cases.bind('<<ComboboxSelected>>', self._on_case_selected)

        # Botón para guardar el texto actual con un nombre personalizado
        save_btn = tk.Button(
            sel_frame,
            text='💾 Guardar',
            font=('Segoe UI', 9, 'bold'),
            bg=COLORS['accent'],
            fg='white',
            activebackground=COLORS['accent_light'],
            activeforeground='white',
            relief='flat',
            bd=0,
            padx=8, pady=4,
            cursor='hand2',
            command=self._on_save_case_dialog
        )
        save_btn.pack(side='left')

        # Botón para borrar el caso seleccionado
        del_btn = tk.Button(
            sel_frame,
            text='✕',
            font=('Segoe UI', 9, 'bold'),
            bg=COLORS['bg_input'],
            fg=COLORS['danger'],
            activebackground=COLORS['border'],
            activeforeground=COLORS['danger'],
            relief='flat',
            bd=0,
            padx=6, pady=4,
            cursor='hand2',
            command=self._on_delete_case
        )
        del_btn.pack(side='left', padx=(4, 0))

        ttk.Separator(parent, orient='horizontal').pack(fill='x', pady=6, padx=10)

        self._section_label(parent, '📝  Base de Conocimiento Actual')

        instr = (
            'Escribe tus reglas en español (una por línea o separadas con punto).\n'
            'Todo se auto-guarda al salir o cambiar de texto.'
        )
        tk.Label(
            parent, text=instr,
            font=('Segoe UI', 9), bg=COLORS['bg_panel'],
            fg=COLORS['text_dim'], justify='left', padx=12, pady=2,
            wraplength=340
        ).pack(fill='x')

        # Área de texto
        txt_frame = tk.Frame(parent, bg=COLORS['bg_panel'])
        txt_frame.pack(fill='both', expand=True, padx=10, pady=(6, 4))

        self.input_text = tk.Text(
            txt_frame,
            font=self.font_code,
            bg=COLORS['bg_input'],
            fg=COLORS['text_main'],
            insertbackground=COLORS['accent_light'],
            selectbackground=COLORS['accent'],
            relief='flat',
            bd=6,
            padx=10, pady=10,
            wrap='word',
            height=12
        )
        self.input_text.pack(side='left', fill='both', expand=True)

        scrollbar_in = ttk.Scrollbar(txt_frame, command=self.input_text.yview)
        scrollbar_in.pack(side='right', fill='y')
        self.input_text.configure(yscrollcommand=scrollbar_in.set)

        # Cargar el último texto que tenía el usuario al cerrar
        self.input_text.insert('1.0', self.last_text)

        # Cada vez que el usuario edite o teclee algo, guardar memoria temporal
        self.input_text.bind('<KeyRelease>', lambda e: self._save_storage())

        ttk.Separator(parent, orient='horizontal').pack(fill='x', pady=6, padx=10)

        # Botón de análisis
        btn = tk.Button(
            parent,
            text='⚡  Analizar Base de Conocimiento',
            font=self.font_header,
            bg=COLORS['btn_bg'],
            fg=COLORS['btn_text'],
            activebackground=COLORS['btn_hover'],
            activeforeground='white',
            relief='flat',
            bd=0,
            padx=16, pady=11,
            cursor='hand2',
            command=self._on_analyze
        )
        btn.pack(fill='x', padx=10, pady=(0, 4))
        btn.bind('<Enter>', lambda e: btn.configure(bg=COLORS['btn_hover']))
        btn.bind('<Leave>', lambda e: btn.configure(bg=COLORS['btn_bg']))

        # Barra de botones secundarios (Limpiar y Guardar manual)
        btn_bar = tk.Frame(parent, bg=COLORS['bg_panel'])
        btn_bar.pack(fill='x', padx=10, pady=(0, 8))

        clear_btn = tk.Button(
            btn_bar,
            text='🗑  Limpiar',
            font=self.font_body,
            bg=COLORS['bg_input'],
            fg=COLORS['text_dim'],
            activebackground=COLORS['border'],
            activeforeground=COLORS['text_main'],
            relief='flat',
            bd=0,
            padx=10, pady=5,
            cursor='hand2',
            command=self._on_clear
        )
        clear_btn.pack(side='left', fill='x', expand=True, padx=(0, 4))

        quick_save_btn = tk.Button(
            btn_bar,
            text='💾  Auto-Guardar Ahora',
            font=self.font_body,
            bg=COLORS['bg_input'],
            fg=COLORS['info'],
            activebackground=COLORS['border'],
            activeforeground=COLORS['info'],
            relief='flat',
            bd=0,
            padx=10, pady=5,
            cursor='hand2',
            command=self._manual_quick_save
        )
        quick_save_btn.pack(side='right', fill='x', expand=True)

    def _refresh_combobox_values(self):
        """Actualiza la lista desplegable de casos guardados."""
        names = list(self.saved_cases.keys())
        self.combo_cases['values'] = names
        if names:
            self.combo_cases.set('Seleccionar o cargar texto...')

    def _on_case_selected(self, event=None):
        """Carga el texto seleccionado desde el combobox."""
        selected_name = self.case_var.get()
        if selected_name in self.saved_cases:
            self.input_text.delete('1.0', 'end')
            self.input_text.insert('1.0', self.saved_cases[selected_name])
            self._save_storage()

    def _on_save_case_dialog(self):
        """Abre un diálogo para que el usuario guarde el texto actual con un nombre."""
        current_text = self.input_text.get('1.0', 'end').strip()
        if not current_text:
            messagebox.showwarning("Texto vacío", "Escribe algunas reglas antes de guardarlas.")
            return

        name = simpledialog.askstring(
            "Guardar Caso",
            "Introduce un nombre para este caso o base de conocimiento:",
            parent=self.root
        )
        if name and name.strip():
            name = name.strip()
            self.saved_cases[name] = current_text
            self._save_storage()
            self._refresh_combobox_values()
            self.case_var.set(name)
            messagebox.showinfo("Guardado", f"Caso '{name}' guardado correctamente.")

    def _on_delete_case(self):
        """Elimina el caso personalizado seleccionado del combobox."""
        selected_name = self.case_var.get()
        if not selected_name or selected_name not in self.saved_cases:
            messagebox.showwarning("Selección", "Selecciona un caso de la lista para eliminar.")
            return

        if selected_name in PRESET_EXAMPLES:
            messagebox.showwarning("Protegido", "Los ejemplos predeterminados no se pueden eliminar.")
            return

        if messagebox.askyesno("Eliminar", f"¿Deseas eliminar el caso '{selected_name}'?"):
            del self.saved_cases[selected_name]
            self._save_storage()
            self._refresh_combobox_values()
            messagebox.showinfo("Eliminado", f"El caso '{selected_name}' ha sido eliminado.")

    def _manual_quick_save(self):
        """Guardado rápido manual."""
        self._save_storage()
        messagebox.showinfo("Guardado", "Estado y texto actual guardados en disco correctamente.")

    def _build_results_panel(self, parent: tk.Frame):
        notebook = ttk.Notebook(parent, style='TNotebook')
        notebook.pack(fill='both', expand=True)

        # Tab 1: Árbol Tableau Semántico (Visual)
        tab_tree = tk.Frame(notebook, bg=COLORS['bg_panel'])
        notebook.add(tab_tree, text='🌿  Árbol Semántico (Diagrama)')
        self._build_tree_tab(tab_tree)

        # Tab 2: Fórmulas y Reglas con tipo de Conector
        tab_formulas = tk.Frame(notebook, bg=COLORS['bg_panel'])
        notebook.add(tab_formulas, text='📐  Fórmulas y Conectores')
        self._build_formulas_tab(tab_formulas)

        # Tab 3: Pasos Explicativos
        tab_steps = tk.Frame(notebook, bg=COLORS['bg_panel'])
        notebook.add(tab_steps, text='📋  Pasos de Expansión')
        self._build_steps_tab(tab_steps)

        # Tab 4: Átomos
        tab_atoms = tk.Frame(notebook, bg=COLORS['bg_panel'])
        notebook.add(tab_atoms, text='🔤  Átomos Proposicionales')
        self._build_atoms_tab(tab_atoms)

        # Tab 5: Resultados
        tab_result = tk.Frame(notebook, bg=COLORS['bg_panel'])
        notebook.add(tab_result, text='✅  Resultados y Modelos')
        self._build_result_tab(tab_result)

        self.notebook = notebook

    def _build_atoms_tab(self, parent: tk.Frame):
        self._section_label(parent, 'Tabla de Proposiciones Atómicas')
        tk.Label(
            parent,
            text='Mapeo unívoco entre las proposiciones simples en lenguaje natural y sus letras proposicionales.',
            font=self.font_body, bg=COLORS['bg_panel'],
            fg=COLORS['text_dim'], padx=14, pady=4
        ).pack(anchor='w')

        frame = tk.Frame(parent, bg=COLORS['bg_panel'])
        frame.pack(fill='both', expand=True, padx=14, pady=8)

        self.atoms_tree = ttk.Treeview(
            frame,
            columns=('letra', 'proposicion'),
            show='headings',
            style='Tableau.Treeview'
        )
        self.atoms_tree.heading('letra',       text='Letra')
        self.atoms_tree.heading('proposicion', text='Proposición Simple (Significado en Lenguaje Natural)')
        self.atoms_tree.column('letra',       width=80,  anchor='center')
        self.atoms_tree.column('proposicion', width=650, anchor='w')

        sb = ttk.Scrollbar(frame, command=self.atoms_tree.yview)
        self.atoms_tree.configure(yscrollcommand=sb.set)
        self.atoms_tree.pack(side='left', fill='both', expand=True)
        sb.pack(side='right', fill='y')

        self.atoms_tree.tag_configure('odd',  background='#1E2030')
        self.atoms_tree.tag_configure('even', background=COLORS['bg_tree'])

    def _build_formulas_tab(self, parent: tk.Frame):
        self._section_label(parent, 'Fórmulas Bien Formadas (WFF) y Clasificación de Conectores')
        tk.Label(
            parent,
            text='Cada regla procesada muestra su fórmula lógica y el conector lógico principal que la gobierna.',
            font=self.font_body, bg=COLORS['bg_panel'],
            fg=COLORS['text_dim'], padx=14, pady=4
        ).pack(anchor='w')

        frame = tk.Frame(parent, bg=COLORS['bg_panel'])
        frame.pack(fill='both', expand=True, padx=14, pady=8)

        self.formulas_tree = ttk.Treeview(
            frame,
            columns=('id', 'formula', 'conector', 'texto'),
            show='headings',
            style='Tableau.Treeview'
        )
        self.formulas_tree.heading('id',       text='Regla')
        self.formulas_tree.heading('formula',  text='Fórmula Lógica')
        self.formulas_tree.heading('conector', text='Tipo de Conector Principal')
        self.formulas_tree.heading('texto',    text='Texto en Lenguaje Natural')

        self.formulas_tree.column('id',       width=60,  anchor='center')
        self.formulas_tree.column('formula',  width=200, anchor='w')
        self.formulas_tree.column('conector', width=240, anchor='w')
        self.formulas_tree.column('texto',    width=450, anchor='w')

        sb = ttk.Scrollbar(frame, command=self.formulas_tree.yview)
        self.formulas_tree.configure(yscrollcommand=sb.set)
        self.formulas_tree.pack(side='left', fill='both', expand=True)
        sb.pack(side='right', fill='y')

        self.formulas_tree.tag_configure('odd',  background='#1E2030')
        self.formulas_tree.tag_configure('even', background=COLORS['bg_tree'])

    def _build_tree_tab(self, parent: tk.Frame):
        self._section_label(parent, 'Diagrama Semántico del Árbol de Tableaux')

        legend_frame = tk.Frame(parent, bg=COLORS['bg_panel'])
        legend_frame.pack(fill='x', padx=14, pady=4)

        legends = [
            ('■ Raíz', COLORS['accent'], 'Premisas Iniciales'),
            ('■ Bloque', COLORS['node_bg'], 'Fórmulas de la Rama'),
            ('✕ CERRADA', COLORS['danger'], 'Contradicción encontrada (Rama Refutada)'),
            ('◉ ABIERTA', COLORS['success'], 'Rama Consistente (Modelo Satisfacible)'),
        ]
        for sym, col, desc in legends:
            f = tk.Frame(legend_frame, bg=COLORS['bg_panel'])
            f.pack(side='left', padx=10)
            tk.Label(f, text=sym, font=('Segoe UI', 9, 'bold'), bg=COLORS['bg_panel'],
                     fg=col).pack(side='left')
            tk.Label(f, text=f': {desc}', font=self.font_body,
                     bg=COLORS['bg_panel'], fg=COLORS['text_dim']).pack(side='left')

        paned = tk.PanedWindow(parent, orient='vertical',
                               bg=COLORS['bg_main'], sashwidth=6,
                               sashrelief='flat')
        paned.pack(fill='both', expand=True, padx=14, pady=6)

        canvas_frame = tk.Frame(paned, bg=COLORS['bg_tree'])
        paned.add(canvas_frame, minsize=320)

        self.tree_canvas = tk.Canvas(
            canvas_frame,
            bg=COLORS['bg_tree'],
            highlightthickness=0,
            bd=0
        )
        hscroll = ttk.Scrollbar(canvas_frame, orient='horizontal',
                                 command=self.tree_canvas.xview)
        vscroll = ttk.Scrollbar(canvas_frame, orient='vertical',
                                 command=self.tree_canvas.yview)
        self.tree_canvas.configure(
            xscrollcommand=hscroll.set,
            yscrollcommand=vscroll.set
        )
        hscroll.pack(side='bottom', fill='x')
        vscroll.pack(side='right',  fill='y')
        self.tree_canvas.pack(side='left', fill='both', expand=True)

        branches_frame = tk.Frame(paned, bg=COLORS['bg_panel'])
        paned.add(branches_frame, minsize=140)

        self._section_label(branches_frame, 'Estado Terminal de Ramas (Hojas)', small=True)

        self.branches_tree = ttk.Treeview(
            branches_frame,
            columns=('rama', 'estado', 'formulas', 'modelo'),
            show='headings',
            style='Tableau.Treeview'
        )
        self.branches_tree.heading('rama',     text='Rama')
        self.branches_tree.heading('estado',   text='Estado')
        self.branches_tree.heading('formulas', text='Fórmulas acumuladas en la Rama')
        self.branches_tree.heading('modelo',   text='Asignación de Verdad / Causa de Cierre')
        self.branches_tree.column('rama',     width=70,  anchor='center')
        self.branches_tree.column('estado',   width=130, anchor='center')
        self.branches_tree.column('formulas', width=520, anchor='w')
        self.branches_tree.column('modelo',   width=320, anchor='w')

        sb2 = ttk.Scrollbar(branches_frame, command=self.branches_tree.yview)
        self.branches_tree.configure(yscrollcommand=sb2.set)
        self.branches_tree.pack(side='left', fill='both', expand=True, padx=6, pady=4)
        sb2.pack(side='right', fill='y', pady=4)

        self.branches_tree.tag_configure('open',   foreground=COLORS['success'])
        self.branches_tree.tag_configure('closed', foreground=COLORS['danger'])

    def _build_steps_tab(self, parent: tk.Frame):
        self._section_label(parent, 'Bitácora Explicativa de Expansión del Tableau')
        tk.Label(
            parent,
            text='Cada paso describe en detalle la regla lógica aplicada (Alfa o Beta), la fórmula de origen y la justificación formal.',
            font=self.font_body, bg=COLORS['bg_panel'],
            fg=COLORS['text_dim'], padx=14, pady=4
        ).pack(anchor='w')

        frame = tk.Frame(parent, bg=COLORS['bg_panel'])
        frame.pack(fill='both', expand=True, padx=14, pady=8)

        self.steps_tree = ttk.Treeview(
            frame,
            columns=('paso', 'tipo', 'regla', 'formula', 'rama', 'explicacion'),
            show='headings',
            style='Tableau.Treeview'
        )
        self.steps_tree.heading('paso',        text='#')
        self.steps_tree.heading('tipo',        text='Clasificación')
        self.steps_tree.heading('regla',       text='Regla Lógica')
        self.steps_tree.heading('formula',     text='Fórmula Evaluada')
        self.steps_tree.heading('rama',        text='Rama')
        self.steps_tree.heading('explicacion', text='Explicación y Justificación Lógica')

        self.steps_tree.column('paso',        width=40,  anchor='center')
        self.steps_tree.column('tipo',        width=120, anchor='center')
        self.steps_tree.column('regla',       width=230, anchor='w')
        self.steps_tree.column('formula',     width=130, anchor='center')
        self.steps_tree.column('rama',        width=60,  anchor='center')
        self.steps_tree.column('explicacion', width=580, anchor='w')

        sb = ttk.Scrollbar(frame, command=self.steps_tree.yview)
        self.steps_tree.configure(yscrollcommand=sb.set)
        self.steps_tree.pack(side='left', fill='both', expand=True)
        sb.pack(side='right', fill='y')

        self.steps_tree.tag_configure('alpha',  background='#1E2640')
        self.steps_tree.tag_configure('beta',   background='#261E38')

    def _build_result_tab(self, parent: tk.Frame):
        self._section_label(parent, 'Resultado del Análisis Lógico')

        result_frame = tk.Frame(parent, bg=COLORS['bg_panel'])
        result_frame.pack(fill='both', expand=True, padx=14, pady=8)

        self.result_text = tk.Text(
            result_frame,
            font=self.font_result,
            bg=COLORS['bg_input'],
            fg=COLORS['text_main'],
            relief='flat',
            bd=8,
            padx=16, pady=16,
            wrap='word',
            state='disabled',
            cursor='arrow'
        )
        sb = ttk.Scrollbar(result_frame, command=self.result_text.yview)
        self.result_text.configure(yscrollcommand=sb.set)
        self.result_text.pack(side='left', fill='both', expand=True)
        sb.pack(side='right', fill='y')

        self.result_text.tag_configure('title',
            font=('Segoe UI', 14, 'bold'), foreground=COLORS['accent_light'],
            spacing1=10, spacing3=6
        )
        self.result_text.tag_configure('section',
            font=('Consolas', 11, 'bold'), foreground=COLORS['warning'],
            spacing1=8, spacing3=2
        )
        self.result_text.tag_configure('model',
            font=('Consolas', 13), foreground=COLORS['text_code'],
            lmargin1=30, lmargin2=30
        )
        self.result_text.tag_configure('unsat',
            font=('Segoe UI', 13, 'bold'), foreground=COLORS['danger'],
            spacing1=10
        )
        self.result_text.tag_configure('success_tag',
            font=('Segoe UI', 12, 'bold'), foreground=COLORS['success'],
            spacing1=6
        )
        self.result_text.tag_configure('dim',
            font=('Segoe UI', 10), foreground=COLORS['text_dim'],
            lmargin1=20
        )

    def _section_label(self, parent, text: str, small: bool = False):
        f = tk.Frame(parent, bg=COLORS['bg_panel'])
        f.pack(fill='x', padx=10, pady=(10, 2))

        lbl_font = self.font_body if small else self.font_header
        tk.Label(
            f, text=text,
            font=lbl_font,
            bg=COLORS['bg_panel'],
            fg=COLORS['accent_light'],
            padx=4
        ).pack(side='left')

        sep = tk.Frame(f, bg=COLORS['accent'], height=2)
        sep.pack(side='left', fill='x', expand=True, padx=6, pady=4)

    def _on_clear(self):
        self.input_text.delete('1.0', 'end')
        self._save_storage()

    def _on_analyze(self):
        raw = self.input_text.get('1.0', 'end').strip()
        if not raw:
            messagebox.showwarning(
                'Entrada vacía',
                'Por favor, escribe al menos una regla en la Base de Conocimiento.'
            )
            return

        # Auto-guardar el texto actual al analizar
        self._save_storage()

        try:
            parser = NLPParser()
            parsed = parser.parse_knowledge_base(raw)

            if not parsed:
                messagebox.showerror(
                    'Sin fórmulas',
                    'No se pudieron extraer fórmulas del texto proporcionado.\n'
                    'Verifica la sintaxis de las oraciones.'
                )
                return

            formulas = [f for _, f in parsed]

            engine = TableauxEngine()
            engine.initialize(formulas)
            engine.run()

            self._update_atoms_tab(parser)
            self._update_formulas_tab(parsed)
            self._update_tree_tab(engine)
            self._update_steps_tab(engine)
            self._update_result_tab(engine, parser)

            # Abrir directamente en la pestaña del árbol semántico
            self.notebook.select(0)

        except Exception as e:
            messagebox.showerror(
                'Error en el análisis',
                f'Ocurrió un error inesperado:\n{str(e)}\n\n'
                'Revisa la sintaxis de las oraciones.'
            )
            raise

    def _update_atoms_tab(self, parser: NLPParser):
        for item in self.atoms_tree.get_children():
            self.atoms_tree.delete(item)

        for i, (letter, description) in enumerate(
            sorted(parser.atom_descriptions.items())
        ):
            tag = 'odd' if i % 2 else 'even'
            self.atoms_tree.insert(
                '', 'end',
                values=(letter, description),
                tags=(tag,)
            )

    def _update_formulas_tab(self, parsed: List[Tuple[str, Formula]]):
        for item in self.formulas_tree.get_children():
            self.formulas_tree.delete(item)

        for i, (text, formula) in enumerate(parsed):
            tag = 'odd' if i % 2 else 'even'
            conector_desc = formula.connector_description()
            self.formulas_tree.insert(
                '', 'end',
                values=(f'R{i+1}', str(formula), conector_desc, text),
                tags=(tag,)
            )

    def _update_steps_tab(self, engine: TableauxEngine):
        for item in self.steps_tree.get_children():
            self.steps_tree.delete(item)

        for i, step in enumerate(engine.steps):
            is_beta = step.get('splits', False)
            tag = 'beta' if is_beta else 'alpha'
            self.steps_tree.insert(
                '', 'end',
                values=(
                    i + 1,
                    step['rule'],
                    step['rule_name'],
                    step['from'],
                    f"B{step['branch']}",
                    step['explanation']
                ),
                tags=(tag,)
            )

    def _update_tree_tab(self, engine: TableauxEngine):
        for item in self.branches_tree.get_children():
            self.branches_tree.delete(item)

        all_atoms = engine.all_atoms

        for branch in engine.branches:
            formulas_str = '  ·  '.join(str(n.formula) for n in branch.nodes)
            if branch.closed:
                estado = '✕  CERRADA'
                modelo = f'Contradicción: {branch.close_reason}'
                tag = 'closed'
            else:
                estado = '◉  ABIERTA'
                m = branch.model(all_atoms)
                modelo = '  '.join(f'{k}={("V" if v else "F")}' for k, v in sorted(m.items()))
                tag = 'open'

            self.branches_tree.insert(
                '', 'end',
                values=(f'B{branch.id}', estado, formulas_str, modelo),
                tags=(tag,)
            )

        self._draw_semantic_tree_diagram(engine)

    def _draw_semantic_tree_diagram(self, engine: TableauxEngine):
        canvas = self.tree_canvas
        canvas.delete('all')

        if not engine.root:
            return

        def count_leaves(node: TableauBranch) -> int:
            if not node.children:
                return 1
            return sum(count_leaves(c) for c in node.children)

        def tree_depth(node: TableauBranch) -> int:
            if not node.children:
                return 1
            return 1 + max(tree_depth(c) for c in node.children)

        total_leaves = count_leaves(engine.root)
        depth = tree_depth(engine.root)

        col_width = 240
        level_height = 160
        margin_x = 60
        margin_y = 50

        total_width = max(1100, total_leaves * col_width + margin_x * 2)
        total_height = max(700, depth * level_height + margin_y * 2 + 80)
        canvas.configure(scrollregion=(0, 0, total_width, total_height))

        positions = {}
        leaf_counter = [0]

        def compute_positions(branch: TableauBranch, current_depth: int):
            y = margin_y + current_depth * level_height
            if not branch.children:
                x = margin_x + leaf_counter[0] * col_width + col_width / 2
                leaf_counter[0] += 1
                positions[branch.id] = (x, y)
                return x
            else:
                child_xs = [compute_positions(child, current_depth + 1) for child in branch.children]
                x = sum(child_xs) / len(child_xs)
                positions[branch.id] = (x, y)
                return x

        compute_positions(engine.root, 0)

        def draw_edges(branch: TableauBranch):
            px, py = positions[branch.id]
            for child in branch.children:
                cx, cy = positions[child.id]

                canvas.create_line(
                    px, py + 25, cx, cy - 25,
                    fill=COLORS['accent_light'], width=2, smooth=True
                )

                if child.branch_label:
                    mid_x = (px + cx) / 2
                    mid_y = (py + cy) / 2
                    canvas.create_rectangle(
                        mid_x - 35, mid_y - 10, mid_x + 35, mid_y + 10,
                        fill=COLORS['bg_main'], outline=COLORS['border']
                    )
                    canvas.create_text(
                        mid_x, mid_y,
                        text=child.branch_label,
                        fill=COLORS['warning'],
                        font=('Consolas', 9, 'bold')
                    )

                draw_edges(child)

        draw_edges(engine.root)

        def draw_nodes(branch: TableauBranch):
            x, y = positions[branch.id]

            if branch.parent is None:
                title = f"Raíz (B{branch.id})"
                lines = [str(n.formula) for n in branch.nodes]
                bg_color = COLORS['accent']
                border_color = COLORS['accent_light']
            else:
                title = f"Rama B{branch.id}"
                lines = [str(f) for f in branch.step_added_formulas]
                if not lines:
                    lines = [str(n.formula) for n in branch.nodes[-2:]]
                bg_color = COLORS['node_bg']
                border_color = COLORS['node_border']

            box_w = 170
            box_h = max(52, 28 + len(lines) * 18)

            x1 = x - box_w / 2
            y1 = y - box_h / 2
            x2 = x + box_w / 2
            y2 = y + box_h / 2

            canvas.create_rectangle(
                x1, y1, x2, y2,
                fill=bg_color, outline=border_color, width=2
            )

            canvas.create_text(
                x, y1 + 12,
                text=title,
                fill='white',
                font=('Segoe UI', 9, 'bold')
            )

            curr_y = y1 + 28
            for f_str in lines:
                canvas.create_text(
                    x, curr_y,
                    text=f_str,
                    fill=COLORS['text_code'],
                    font=('Consolas', 9, 'bold')
                )
                curr_y += 18

            if not branch.children:
                badge_y = y2 + 18
                if branch.closed:
                    canvas.create_rectangle(
                        x - 70, badge_y - 12, x + 70, badge_y + 12,
                        fill=COLORS['danger'], outline=''
                    )
                    canvas.create_text(
                        x, badge_y,
                        text=f"✕ CERRADA\n({branch.close_reason})",
                        fill='white',
                        font=('Consolas', 8, 'bold'),
                        justify='center'
                    )
                else:
                    m = branch.model(engine.all_atoms)
                    model_str = ', '.join(f'{k}={"V" if v else "F"}' for k, v in sorted(m.items()))
                    canvas.create_rectangle(
                        x - 75, badge_y - 12, x + 75, badge_y + 12,
                        fill=COLORS['success'], outline=''
                    )
                    canvas.create_text(
                        x, badge_y,
                        text=f"◉ ABIERTA\n{model_str}",
                        fill='white',
                        font=('Consolas', 8, 'bold'),
                        justify='center'
                    )

            for child in branch.children:
                draw_nodes(child)

        draw_nodes(engine.root)

    def _update_result_tab(self, engine: TableauxEngine, parser: NLPParser):
        txt = self.result_text
        txt.configure(state='normal')
        txt.delete('1.0', 'end')

        txt.insert('end', '\n  Resultado del Análisis Lógico por Tableaux Semánticos\n', 'title')
        txt.insert('end', '  ' + '─' * 55 + '\n\n', 'dim')

        total    = len(engine.branches)
        closed   = sum(1 for b in engine.branches if b.closed)
        open_cnt = total - closed

        stats = (
            f'  Total de ramas terminales (hojas):  {total}\n'
            f'  Ramas refutadas / cerradas ✕:       {closed}\n'
            f'  Ramas consistentes / abiertas ◉:    {open_cnt}\n'
        )
        txt.insert('end', stats, 'dim')
        txt.insert('end', '\n')

        if engine.is_unsatisfiable():
            txt.insert('end', '  ✕  BASE DE CONOCIMIENTO CONTRADICTORIA (INSATISFACIBLE)\n', 'unsat')
            txt.insert('end',
                '  Todas las ramas del árbol se cerraron por contradicción lógica (A y ¬A).\n'
                '  Por lo tanto, la Base de Conocimiento es inconsistente y no admite ningún modelo.\n',
                'dim'
            )
        else:
            txt.insert('end', '  ◉  BASE DE CONOCIMIENTO CONSISTENTE (SATISFACIBLE)\n\n', 'success_tag')
            models = engine.models()
            txt.insert('end',
                f'  Se encontraron {len(models)} modelo(s) que satisfacen todas las reglas simultáneamente:\n\n',
                'dim'
            )

            atom_desc = parser.atom_descriptions

            for idx, model in enumerate(models):
                branch = engine.open_branches()[idx]
                txt.insert('end',
                    f'  ── Modelo {idx + 1} (Rama B{branch.id}) ──\n',
                    'section'
                )

                for atom, value in sorted(model.items()):
                    val_str = 'V (Verdadero)' if value else 'F (Falso)'
                    desc    = atom_desc.get(atom, '')
                    line    = f'    {atom} = {val_str:<15}  [{desc}]\n'
                    txt.insert('end', line, 'model')

                txt.insert('end', '\n')

            txt.insert('end', '  ── Resumen de Modelos ──\n', 'section')
            for idx, model in enumerate(models):
                compact = '  '.join(
                    f'{k}={"V" if v else "F"}'
                    for k, v in sorted(model.items())
                )
                txt.insert('end', f'    Modelo {idx+1}:  {compact}\n', 'model')

        txt.configure(state='disabled')


# ─────────────────────────────────────────────────────────────────────────────
#  PUNTO DE ENTRADA
# ─────────────────────────────────────────────────────────────────────────────

def main():
    root = tk.Tk()
    app  = TableauxGUI(root)
    root.mainloop()


if __name__ == '__main__':
    main()
