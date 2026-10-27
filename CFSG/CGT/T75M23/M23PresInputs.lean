module

public import CFSG.CGT.T75M23.N7Rels
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.Sporadic.Th.Native

abbrev M23Word : Type := List (Fin 7 × Bool)

@[expose] def liftWord7 (w : List (Fin 6 × Bool)) : M23Word :=
  w.map fun p => (Fin.castSucc p.1, p.2)

@[expose] def invWord7 {m : ℕ} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.reverse).map fun p => (p.1, !p.2)

@[expose] def subst7 {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | a :: u => f a ++ subst7 f u

@[expose] def m23RelsN : List M23Word := rels7.map liftWord7

@[expose] def dGen7 : Fin 3 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true)],
   [(0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true)],
   [(1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (2, true), (5, true)]]

@[expose] def dTheta7 : Fin 3 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true)],
   [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true),
    (1, true), (0, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (1, true), (1, true), (3, true), (4, true)]]

@[expose] def vGen7 : Fin 2 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true)],
   [(0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (1, true), (0, true), (1, true), (5, true)]]

@[expose] def thetaRels7 : List M23Word :=
  [(6, true), (6, true)] ::
    List.ofFn fun i : Fin 3 =>
      [(6, true)] ++ liftWord7 (dGen7 i) ++ [(6, true)] ++ liftWord7 (invWord7 (dTheta7 i))

@[expose] def pWords7 : List (List (Fin 3 × Bool)) :=
  [[(0, true), (2, true), (1, true), (0, true), (2, true), (1, false), (2, true), (1, false),
    (1, false)]]

@[expose] def base3Z : Fin 3 → M23Word :=
  ![liftWord7 (vGen7 0), liftWord7 (vGen7 1), [(6, true)]]

@[expose] def expand3Z : List (Fin 3 × Bool) → M23Word :=
  subst7 fun p => if p.2 then base3Z p.1 else invWord7 (base3Z p.1)

@[expose] def pRels7 : List M23Word := pWords7.map expand3Z

@[expose] def m23Rels : List M23Word := m23RelsN ++ thetaRels7 ++ pRels7

abbrev m23RelsN6 := restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) m23Rels

@[expose] def m23Enum7 : Bool := subsetCheck m23Rels [0, 1, 2, 3, 4, 5] 200000 253

abbrev m23RelsK := restrictWords (subsetOf _ [0, 1]) m23RelsN6

@[expose] def m23Enum6 : Bool := subsetCheck m23RelsN6 [0, 1] 200000 16

@[expose] def m23Enum2 : Bool := subsetCheck m23RelsK [] 20000 2520

@[expose] def m23tA : Table :=
  #[1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] def m23tB : Table :=
  #[15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] def m23GenWord : ℕ → List ℤ
  | 0 => [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1,
      2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2,
      2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2,
      2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]
  | 1 => [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2,
      2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 1,
      2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2]
  | 2 => [1]
  | 3 => [2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1,
      2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2,
      1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1,
      2, 1]
  | 4 => [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2,
      1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2,
      1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2]
  | 5 => [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1,
      2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2,
      2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2,
      2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1,
      1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1]
  | 6 => [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2,
      1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1,
      2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
      2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1,
      2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1]
  | _ => []

@[expose] def m23SurjACodes : List ℕ := [4]

@[expose] def m23SurjBCodes : List ℕ := [0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 6, 10, 12,
    0, 2, 2, 12, 0, 2]

@[expose] def m23OfCodes (c : List ℕ) : M23Word :=
  c.map fun x => (⟨x / 2 % 7, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0))

@[expose] def m23LetterZ (l : Fin 7 × Bool) : ℤ :=
  if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def m23SurjA : List ℤ := (m23OfCodes m23SurjACodes).map m23LetterZ

@[expose] def m23SurjB : List ℤ := (m23OfCodes m23SurjBCodes).map m23LetterZ

@[expose] def m23AB (z : ℤ) : Table := if z = 1 then m23tA else if z = 2 then m23tB else idT 23

@[expose] def m23Img (k : ℕ) : Table := wordT 23 m23AB (m23GenWord k)

@[expose] def m23ImgLetter (T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6 : Table) (z : ℤ) : Table :=
  if z = 1 then T0 else if z = 2 then T1 else if z = 3 then T2 else if z = 4 then T3
  else if z = 5 then T4 else if z = 6 then T5 else if z = 7 then T6 else if z = -1 then V0
  else if z = -2 then V1 else if z = -3 then V2 else if z = -4 then V3 else if z = -5 then V4
  else if z = -6 then V5 else V6

@[noinline, expose] def m23TabCheck : Bool :=
  let T0 := m23Img 0
  let T1 := m23Img 1
  let T2 := m23Img 2
  let T3 := m23Img 3
  let T4 := m23Img 4
  let T5 := m23Img 5
  let T6 := m23Img 6
  let V0 := invT 23 T0
  let V1 := invT 23 T1
  let V2 := invT 23 T2
  let V3 := invT 23 T3
  let V4 := invT 23 T4
  let V5 := invT 23 T5
  let V6 := invT 23 T6
  invOK 23 T0 V0 && invOK 23 T1 V1 && invOK 23 T2 V2 && invOK 23 T3 V3 && invOK 23 T4 V4 &&
    invOK 23 T5 V5 && invOK 23 T6 V6 &&
    m23Rels.all (fun r =>
      wordT 23 (m23ImgLetter T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6) (r.map m23LetterZ) ==
        idT 23) &&
    wordT 23 (m23ImgLetter T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6) m23SurjA == m23tA &&
    wordT 23 (m23ImgLetter T0 T1 T2 T3 T4 T5 T6 V0 V1 V2 V3 V4 V5 V6) m23SurjB == m23tB

@[expose] def m23Enums : Bool := m23Enum7 && m23Enum6 && m23Enum2

@[expose] def m23Checks : Bool := m23Enums && m23TabCheck

end CFSG.CGT.T75M23
