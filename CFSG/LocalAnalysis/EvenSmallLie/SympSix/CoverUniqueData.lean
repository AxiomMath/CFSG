module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs

public section

namespace CFSG.EvenSmallLie.SympSix

open CFSG.LieType.Multipliers CFSG.CosetTable CFSG.Sporadic.Schreier CFSG.EvenSmallLie.Sp6

@[expose] def sympA : Equiv.Perm (Fin 36) :=
  tab (evalCodes sp6Gens [2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1])

@[expose] def sympB : Equiv.Perm (Fin 36) :=
  tab (evalCodes sp6Gens [-2, -2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1])

@[expose] def sympT : Equiv.Perm (Fin 36) := sp6A

@[expose] def sympGen : Fin 3 → Equiv.Perm (Fin 36)
  | 0 => sympA
  | 1 => sympB
  | 2 => sympT

@[expose] def wordPerm (w : List (Fin 3 × Bool)) : Equiv.Perm (Fin 36) :=
  (w.map fun x => cond x.2 (sympGen x.1) (sympGen x.1)⁻¹).prod

@[expose] def rels : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)],
    [(1, true), (1, true), (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
     (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
     (0, true), (1, true)],
    [(0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false),
     (1, false), (0, true), (1, true), (0, false), (1, false)],
    [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false),
     (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false),
     (0, false), (1, false)],
    [(2, true), (2, true)],
    [(2, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, false), (1, false),
     (0, false), (1, false), (0, false), (1, false)],
    [(2, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false),
     (2, false), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false),
     (1, false)],
    [(2, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true), (0, true),
     (1, true), (2, true), (0, true), (1, true), (2, true), (0, true), (1, true), (2, true),
     (0, true), (1, true), (2, true), (0, true), (1, true)]]

@[expose] def coverPairs : Fin 3 → List (List (Fin 3 × Bool) × List (Fin 3 × Bool))
  | 0 => [([(1, false), (0, true), (1, true), (1, true), (0, true)],
      [(1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false)]),
    ([(0, true), (1, false), (0, true)],
      [(1, false), (1, false)])]
  | 1 => [([(0, true), (1, false)],
      [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true)]),
    ([(1, true), (1, true)],
      [(0, true), (1, true), (0, true)])]
  | 2 => [([(0, true), (2, true), (1, true), (1, true)],
      [(0, true), (1, true), (2, true), (1, true), (1, true), (0, true), (1, false), (2, true),
      (1, false)])]

@[expose] def wordSB : List (Fin 3 × Bool) :=
  [(0, true), (1, false), (0, true), (1, false), (2, true), (1, true), (1, true), (2, true),
   (1, false), (2, false), (1, false)]

abbrev coverWs : List (List (Fin 3 × Bool)) := coverWords rels fun i => commWords (coverPairs i)

abbrev cover₁ : List (List (Fin 2 × Bool)) := restrictWords (subsetOf 3 [0, 1]) coverWs

abbrev relsY : List (List (Fin 2 × Bool)) := restrictWords (subsetOf 3 [0, 1]) rels

end CFSG.EvenSmallLie.SympSix
