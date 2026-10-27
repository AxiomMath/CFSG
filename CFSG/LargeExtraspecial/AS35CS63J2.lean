module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup
open scoped commutatorElement

namespace S63

theorem mem_center_of_commutator_mem_center {Y : Type*} [Group Y] [Group.IsPerfect Y] {w : Y}
    (hw : ∀ u : Y, u⁻¹ * (w * u * w⁻¹) ∈ center Y) : w ∈ center Y := by
  have h := ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (MulAut.conj w).toMonoidHom (fun u => by simpa using hw u)
  rw [mem_center_iff]
  intro u
  have h1 := congrArg (fun φ : Y →* Y => φ u) h
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply] at h1
  calc u * w = w * u * w⁻¹ * w := by rw [h1]
    _ = w * u := by group

end S63

end CFSG.LargeExtraspecial
