module

public import CFSG.LieType.Multipliers.O73DataInputs

public section

namespace CFSG.KC.Misc.O73

open CFSG.LieType.Multipliers.O73 CFSG.YGroups CFSG.YGroups.ModelNative CFSG.Monster.B.Co2.Native
  Matrix

@[expose] def vecsG (VL : List (List ℕ)) (i : ℕ) : Idx → ZMod 3 := vecOf (VL.getD i [])

@[expose] def tTabsG (VL : List (List ℕ)) : Array (Array ℕ) :=
  Array.ofFn fun i : Fin 8 => tabOf (tMat (vecsG VL i))

@[expose] def rTabsG (VL : List (List ℕ)) : Array (Array ℕ) :=
  Array.ofFn fun i : Fin 8 => tabOf (rMat (vecsG VL i))

@[expose] def strOf (l : List ℕ) : String := String.ofList (l.map Char.ofNat)

end CFSG.KC.Misc.O73

end
