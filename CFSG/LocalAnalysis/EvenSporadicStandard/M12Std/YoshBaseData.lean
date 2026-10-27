module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshWord

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.M12

@[expose] def baseT : Fin 5 → Table
  | 0 => tauT
  | 1 => tbl14 bfE
  | 2 => tbl14 bfN
  | 3 => tbl14 bfF
  | 4 => tbl14 pB

@[expose] def baseTi : Fin 5 → Table
  | 0 => tauT
  | 1 => tbl14 bfE⁻¹
  | 2 => tbl14 bfN⁻¹
  | 3 => tbl14 bfF⁻¹
  | 4 => tbl14 pB⁻¹

@[expose] def tblW (w : List (Fin 5 × Bool)) : Table := evalT 14 baseT baseTi w

@[expose] def epsT (T : Table) : ℕ := if (T[12]!).toNat == 13 then 1 else 0

@[expose] def lamT (T : Table) : ℕ :=
  (((List.range 4).flatMap fun i => (List.range 4).filter fun j =>
    i < j && (T[j]!).toNat < (T[i]!).toNat).length) % 2

@[expose] def commT (S T : Table) : Bool := tblEq 14 (compT 14 S T) (compT 14 T S)

@[expose] def wJ : List (Fin 5 × Bool) := [(3, true), (3, true), (3, true), (3, true)]

@[expose] def stepW (α : ℕ) (wm y : List (Fin 5 × Bool)) : Option (List (Fin 5 × Bool)) :=
  if commT (tblW (invW wm ++ y ++ wm)) (tblW wJ) then
    some (y ++ powW (wm ++ wJ ++ invW wm)
      (epsT (tblW (invW wm ++ y ++ wm)) + α * lamT (tblW (invW wm ++ y ++ wm))))
  else none

@[expose] def xAct (α : ℕ) (ws y : List (Fin 5 × Bool)) : Option (List (Fin 5 × Bool)) :=
  (stepW α ws y).bind fun y₁ => (stepW α [] y₁).bind fun y₂ => stepW α (invW ws) y₂

end CFSG.EvenSporadicStandard.M12Std.Yosh
