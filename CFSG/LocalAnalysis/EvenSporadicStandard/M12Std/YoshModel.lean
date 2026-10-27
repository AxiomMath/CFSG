
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelBase

public import Certificates.Certificate26900

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.EvenSporadicStandard.Fin76b CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.M12 AutETable Subgroup

section Certified

theorem yFacts : Spec.Facts := Certificates.certificate26900.1

theorem yEnum : EnumSpec 14 yGens yEl ∧ yEl.size = 384 := Certificates.certificate26900.2

theorem yperm_mem {k : ℕ} (hk : k < 384) : yperm k ∈ yK :=
  yEnum.1.mem k (by rw [yEnum.2]; exact hk)

theorem yelt_coe' {k : ℕ} (hk : k < 384) : (yelt k : Equiv.Perm (Fin 14)) = yperm k :=
  yelt_coe (yperm_mem hk)

theorem yrep {k : ℕ} (hk : k < 384) : Rep 14 yEl[k]! (yperm k) :=
  yEnum.1.rep k (by rw [yEnum.2]; exact hk)

theorem yelt_surj (y : ↥yK) : ∃ a, a < 384 ∧ yelt a = y := by
  obtain ⟨k, hk, hrep⟩ := yEnum.1.cover y.1 y.2
  rw [yEnum.2] at hk
  refine ⟨k, hk, Subtype.ext ?_⟩
  rw [yelt_coe' hk]
  exact (tablePerm_eq hrep)

end Certified

end CFSG.EvenSporadicStandard.M12Std.Yosh
