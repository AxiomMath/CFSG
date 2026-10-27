
module

public import Certificates.Data.Yosh26900Spec

@[expose] public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.EvenSporadicStandard.Fin76b CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.M12 AutETable Subgroup

export Spec (yK)

@[expose] noncomputable def yperm (k : ℕ) : Equiv.Perm (Fin 14) := tablePerm 14 yEl[k]!

open Classical in
@[expose] noncomputable def yelt (k : ℕ) : ↥yK :=
  if h : yperm k ∈ yK then ⟨yperm k, h⟩ else 1

theorem yelt_coe {k : ℕ} (h : yperm k ∈ yK) : (yelt k : Equiv.Perm (Fin 14)) = yperm k := by
  simp [yelt, h]

end CFSG.EvenSporadicStandard.M12Std.Yosh
