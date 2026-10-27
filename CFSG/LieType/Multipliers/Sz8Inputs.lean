module

public import CFSG.LieType.Multipliers.Sz8BridgeInputs

@[expose] public section

namespace CFSG.LieType.Multipliers.Sz8

open TauCeti CFSG.CosetTable

@[expose] def commData : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))
  | 0 => [(parseWord "bb", parseWord "abba"), (parseWord "baBa", parseWord "Baba")]
  | 1 => [(parseWord "aBa", parseWord "bab"), (parseWord "Bab", parseWord "baB")]

@[expose] def wWord (i : Fin 2) : List (Fin 2 × Bool) := commWords (commData i)

@[expose] def kerWords : List (List (Fin 2 × Bool) × ℕ) :=
  [(parseWord relFive, 2), (parseWord relSeven, 2), (parseWord relFive ++ parseWord relSeven, 2),
    (parseWord relFive ++ FreeGroup.invRev (parseWord relSeven), 2),
    (parseWord relFive ++ parseWord relFive ++ FreeGroup.invRev (parseWord relSeven), 2),
    (parseWord relSeven ++ parseWord relSeven ++ FreeGroup.invRev (parseWord relFive), 2)]

end CFSG.LieType.Multipliers.Sz8
