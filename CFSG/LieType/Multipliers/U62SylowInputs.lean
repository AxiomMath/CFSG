module

public import CFSG.LieType.Multipliers.U62KernelInputs

@[expose] public section

namespace CFSG.LieType.Multipliers.U62

open CFSG.CosetTable

abbrev cover₁ : List (List (Fin 4 × Bool)) :=
  restrictWords (subsetOf 5 [0, 1, 2, 3]) coverWs

abbrev coverAB : List (List (Fin 2 × Bool)) := restrictWords (subsetOf _ [0, 1]) cover₁

abbrev sylowWordsAB : List (List (Fin 2 × Bool)) := [[(0, true), (1, true), (0, true),
  (1, true)],
  [(1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, false), (1, false), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, false), (1, false)]]

def sylowRels : List (List (Fin 2 × Bool)) := [[(0, true), (1, false), (0, true),
  (1, false), (0, true), (1, false)],
  [(0, false), (0, false), (1, false), (1, false), (1, false), (0, false)],
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
  [(1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (0, false), (1, false),
    (0, false)]]

def includeAB (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

abbrev sylowWords : List (List (Fin 4 × Bool)) :=
  sylowWordsAB.map (List.map fun l => (includeAB l.1, l.2))

end CFSG.LieType.Multipliers.U62
