module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsDef

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Pointwise

theorem congr_self_symm_apply {Y : Type} [Group Y] (c α : MulAut Y) :
    (MulAut.congr c).symm α = c⁻¹ * α * c := by
  ext y
  simp [MulAut.congr_symm_apply]

end CFSG.EvenSporadicStandard.M22Std
