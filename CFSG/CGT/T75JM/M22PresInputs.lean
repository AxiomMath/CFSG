module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.CFSGNative.Mathieu.M22
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Sporadic.Th.Native CFSG.Sporadic.Mathieu.Native

abbrev M22Word : Type := List (Fin 7 × Bool)

@[expose] def m22RelsN : List M22Word :=
  [[(0, true), (0, true)],
   [(1, true), (1, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
   [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)],
   [(2, true), (2, true)],
   [(2, true), (3, true), (2, true), (3, true)],
   [(2, true), (4, true), (2, true), (4, true)],
   [(2, true), (5, true), (2, true), (5, true)],
   [(3, true), (3, true)],
   [(3, true), (4, true), (3, true), (4, true)],
   [(3, true), (5, true), (3, true), (5, true)],
   [(4, true), (4, true)],
   [(4, true), (5, true), (4, true), (5, true)],
   [(5, true), (5, true)],
   [(0, true), (2, true), (0, false), (2, false)],
   [(0, true), (3, true), (0, false), (5, false), (3, false), (2, false)],
   [(0, true), (4, true), (0, false), (5, false), (4, false)],
   [(0, true), (5, true), (0, false), (5, false)],
   [(1, true), (2, true), (1, false), (5, false), (3, false)],
   [(1, true), (3, true), (1, false), (4, false)],
   [(1, true), (4, true), (1, false), (4, false), (2, false)],
   [(1, true), (5, true), (1, false), (5, false), (2, false)]]

@[expose] def m22RelsY : List M22Word :=
  [[(1, true), (4, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (4, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true)],
   [(1, true), (4, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (6, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (6, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (6, false), (1, true), (0, false), (4, false), (1, false)],
   [(1, true), (4, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (6, false), (6, true), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (1, true), (0, false), (4, false), (1, false), (6, true), (6, true)],
   [(1, true), (4, true), (0, true), (1, false), (1, true), (4, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (4, false), (1, false), (6, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (4, false), (1, false), (6, true), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true)],
   [(1, true), (4, true), (0, true), (1, false), (1, true), (4, true), (0, true), (1, false), (6, false), (1, true), (0, false), (4, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (1, true), (4, true), (0, true), (1, false), (6, true), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true)]]

@[expose] def m22RelsP : List M22Word :=
  [[(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (5, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (5, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (6, true), (6, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (5, false), (6, false), (6, true), (5, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (5, true), (1, true), (1, true), (6, true), (1, false), (1, false), (5, false), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (6, false), (1, false), (1, false), (5, false), (6, false), (6, true), (5, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (5, true), (1, true), (1, true), (6, false), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (5, false), (6, true), (1, false), (1, false), (5, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (6, false), (1, false), (1, false), (5, false)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (6, true), (5, true), (1, true), (1, true), (6, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (5, false), (6, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (6, false), (1, false), (1, false), (5, false)]]

@[expose] def m22Rels : List M22Word := m22RelsN ++ m22RelsY ++ m22RelsP

abbrev m22RelsN6 := restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) m22Rels

@[expose] def m22Enum7 : Bool := subsetCheck m22Rels [0, 1, 2, 3, 4, 5] 200000 77

abbrev m22RelsK := restrictWords (subsetOf _ [0, 1]) m22RelsN6

@[expose] def m22Enum6 : Bool := subsetCheck m22RelsN6 [0, 1] 200000 16

@[expose] def m22Enum2 : Bool := subsetCheck m22RelsK [] 20000 360

@[expose] def m22GenWord : ℕ → List ℤ
  | 0 => [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2]
  | 1 => [2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2]
  | 2 => [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2]
  | 3 => [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2]
  | 4 => [2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2]
  | 5 => [2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2]
  | 6 => [2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]
  | _ => []

@[expose] def m22SurjACodes : List ℕ := [2, 0, 2, 12, 0, 4, 3, 0, 2]

@[expose] def m22SurjBCodes : List ℕ := [2, 6, 12, 0, 6, 12, 0, 12]

@[expose] def m22OfCodes (c : List ℕ) : M22Word :=
  c.map fun x => (⟨x / 2 % 7, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0))

@[expose] def m22LetterZ (l : Fin 7 × Bool) : ℤ :=
  if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def m22SurjA : List ℤ := (m22OfCodes m22SurjACodes).map m22LetterZ

@[expose] def m22SurjB : List ℤ := (m22OfCodes m22SurjBCodes).map m22LetterZ

@[expose] def m22AB (z : ℤ) : Table := if z = 1 then m22Data.tA else if z = 2 then m22Data.tB else idT 22

@[expose] def m22Img (k : ℕ) : Table := wordT 22 m22AB (m22GenWord k)

@[expose] def m22ImgLetter (T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6 : Table) (z : ℤ) : Table :=
  if z = 1 then T0 else if z = 2 then T1 else if z = 3 then T2 else if z = 4 then T3
  else if z = 5 then T4 else if z = 6 then T5 else if z = 7 then T6 else if z = -1 then V0
  else if z = -2 then V1 else if z = -3 then V2 else if z = -4 then V3 else if z = -5 then V4
  else if z = -6 then V5 else V6

@[noinline, expose] def m22TabCheck : Bool :=
  let T0 := m22Img 0
  let T1 := m22Img 1
  let T2 := m22Img 2
  let T3 := m22Img 3
  let T4 := m22Img 4
  let T5 := m22Img 5
  let T6 := m22Img 6
  let V0 := invT 22 T0
  let V1 := invT 22 T1
  let V2 := invT 22 T2
  let V3 := invT 22 T3
  let V4 := invT 22 T4
  let V5 := invT 22 T5
  let V6 := invT 22 T6
  invOK 22 T0 V0 && invOK 22 T1 V1 && invOK 22 T2 V2 && invOK 22 T3 V3 && invOK 22 T4 V4 &&
    invOK 22 T5 V5 && invOK 22 T6 V6 &&
    m22Rels.all (fun r =>
      wordT 22 (m22ImgLetter T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6) (r.map m22LetterZ) ==
        idT 22) &&
    wordT 22 (m22ImgLetter T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6) m22SurjA == m22Data.tA &&
    wordT 22 (m22ImgLetter T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6) m22SurjB == m22Data.tB

@[expose] def m22Enums : Bool := m22Enum7 && m22Enum6 && m22Enum2

@[expose] def m22Checks : Bool := m22Enums && m22TabCheck

end CFSG.CGT.T75JM
