module

public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

@[expose] def mapWord {a b : Nat} (f : Fin a → Fin b) (w : List (Fin a × Bool)) :
    List (Fin b × Bool) :=
  w.map fun p => (f p.1, p.2)

@[expose] def invWord {m : Nat} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.map fun p => (p.1, !p.2)).reverse

@[expose] def a2Words : List (List (Fin 6 × Bool)) :=
  [[(0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)],
  [(4, true), (4, true), (4, true)], [(5, true), (5, true), (5, true)],
  [(2, true), (2, true), (2, true)], [(3, true), (3, true), (3, true)],
  [(0, false), (4, false), (0, true), (4, true), (2, false)],
  [(0, false), (5, false), (0, true), (5, true)],
  [(0, false), (2, false), (0, true), (2, true)],
  [(0, false), (3, false), (0, true), (3, true), (5, false), (5, false)],
  [(1, false), (4, false), (1, true), (4, true)],
  [(1, false), (5, false), (1, true), (5, true), (3, false), (3, false)],
  [(1, false), (2, false), (1, true), (2, true), (4, false)],
  [(1, false), (3, false), (1, true), (3, true)],
  [(4, false), (2, false), (4, true), (2, true)],
  [(4, false), (3, false), (4, true), (3, true), (1, false)],
  [(5, false), (2, false), (5, true), (2, true), (0, false), (0, false)],
  [(5, false), (3, false), (5, true), (3, true)],
  [(0, true), (1, false), (0, true), (1, true), (0, false), (1, true)],
  [(4, true), (5, false), (4, true), (5, true), (4, false), (5, true)],
  [(2, true), (3, false), (2, true), (3, true), (2, false), (3, true)]]

@[expose] def c2Words : List (List (Fin 8 × Bool)) :=
  [[(0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)],
  [(2, true), (2, true), (2, true)], [(3, true), (3, true), (3, true)],
  [(4, true), (4, true), (4, true)], [(5, true), (5, true), (5, true)],
  [(6, true), (6, true), (6, true)], [(7, true), (7, true), (7, true)],
  [(0, false), (2, false), (0, true), (2, true)],
  [(0, false), (3, false), (0, true), (3, true)],
  [(0, false), (4, false), (0, true), (4, true)],
  [(0, false), (5, false), (0, true), (5, true)],
  [(0, false), (6, false), (0, true), (6, true), (2, false), (4, false), (4, false)],
  [(0, false), (7, false), (0, true), (7, true), (3, false), (3, false), (5, false)],
  [(1, false), (2, false), (1, true), (2, true)],
  [(1, false), (3, false), (1, true), (3, true)],
  [(1, false), (4, false), (1, true), (4, true), (2, false), (2, false), (6, false), (6, false)],
  [(1, false), (5, false), (1, true), (5, true), (3, false), (7, false)],
  [(1, false), (6, false), (1, true), (6, true)],
  [(1, false), (7, false), (1, true), (7, true)],
  [(2, false), (4, false), (2, true), (4, true)],
  [(2, false), (5, false), (2, true), (5, true), (0, false), (4, false), (4, false)],
  [(2, false), (6, false), (2, true), (6, true)],
  [(2, false), (7, false), (2, true), (7, true), (1, false), (1, false), (6, false)],
  [(3, false), (4, false), (3, true), (4, true), (0, false), (0, false), (5, false), (5, false)],
  [(3, false), (5, false), (3, true), (5, true)],
  [(3, false), (6, false), (3, true), (6, true), (1, false), (7, false)],
  [(3, false), (7, false), (3, true), (7, true)],
  [(4, false), (5, false), (4, true), (5, true), (0, false)],
  [(4, false), (6, false), (4, true), (6, true), (2, false)],
  [(5, false), (7, false), (5, true), (7, true), (3, false)],
  [(6, false), (7, false), (6, true), (7, true), (1, false)],
  [(0, true), (1, false), (0, true), (1, true), (0, false), (1, true)],
  [(2, true), (3, false), (2, true), (3, true), (2, false), (3, true)],
  [(4, true), (7, false), (4, true), (7, true), (4, false), (7, true)],
  [(5, true), (6, false), (5, true), (6, true), (5, false), (6, true)]]

@[expose] def a2Idx : Fin 6 → Fin 12 := ![4, 5, 6, 7, 9, 10]

@[expose] def c2Idx : Fin 8 → Fin 12 := ![0, 1, 2, 3, 8, 9, 10, 11]

@[expose] def commWords : List (List (Fin 12 × Bool)) :=
  [[(4, false), (2, false), (4, true), (2, true)],
  [(4, false), (3, false), (4, true), (3, true)],
  [(5, false), (2, false), (5, true), (2, true)],
  [(5, false), (3, false), (5, true), (3, true)]]

@[expose] def v6Words : List (List (Fin 12 × Bool)) :=
  a2Words.map (mapWord a2Idx) ++ c2Words.map (mapWord c2Idx) ++ commWords

@[expose] def xPlus : Fin 12 := 9

@[expose] def xMinus : Fin 12 := 10

@[expose] def gluingA : Fin 24 → List (Fin 12 × Bool) :=
  ![[(10, false)], [(9, false)], [(9, true)], [(10, true)], [(10, false)], [(10, false)],
  [(9, false)], [(9, false)], [(9, false), (10, false), (9, true)],
  [(9, false), (10, false), (9, true)], [(9, false), (10, true), (9, true)],
  [(9, false), (10, true), (9, true)], [(9, true)], [(9, true)],
  [(9, true), (10, false), (9, false)], [(9, true), (10, false), (9, false)],
  [(9, true), (10, true), (9, false)], [(9, true), (10, true), (9, false)], [(10, true)],
  [(10, true)], [(9, false), (10, false), (9, true)], [(9, false), (10, true), (9, true)],
  [(9, true), (10, false), (9, false)], [(9, true), (10, true), (9, false)]]

@[expose] def gluingB : Fin 24 → List (Fin 12 × Bool) :=
  ![[(9, false)], [(10, false)], [(10, true)], [(9, true)],
  [(9, false), (10, true), (9, true)], [(9, true), (10, true), (9, false)],
  [(9, false), (10, false), (9, true)], [(9, true), (10, false), (9, false)], [(9, false)],
  [(10, true)], [(10, false)], [(9, true)], [(9, false), (10, true), (9, true)],
  [(9, true), (10, true), (9, false)], [(9, false)], [(10, true)], [(10, false)], [(9, true)],
  [(9, false), (10, false), (9, true)], [(9, true), (10, false), (9, false)],
  [(9, true), (10, true), (9, false)], [(9, true), (10, false), (9, false)],
  [(9, false), (10, true), (9, true)], [(9, false), (10, false), (9, true)]]

@[expose] def substLetter (a b : List (Fin 12 × Bool)) (p : Fin 12 × Bool) :
    List (Fin 12 × Bool) :=
  if p.1 = xPlus then (if p.2 then a else invWord a)
  else if p.1 = xMinus then (if p.2 then b else invWord b) else [p]

@[expose] def v6GluedWords (a b : List (Fin 12 × Bool)) : List (List (Fin 12 × Bool)) :=
  a2Words.map (mapWord a2Idx) ++
    c2Words.map (fun w => (mapWord c2Idx w).flatMap (substLetter a b)) ++ commWords

@[expose] def v6aWords (k : Fin 24) : List (List (Fin 12 × Bool)) :=
  v6GluedWords (gluingA k) (gluingB k)

@[expose] def gluingComplete (k : Fin 24) : Bool := decide (k.val < 4)

end CFSG.ClassicalInvolution.Q3.Q3Z
