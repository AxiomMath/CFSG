module

public import Mathlib.GroupTheory.Solvable

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

universe u v

@[expose] def innerAutomorphismSubgroup (L : Type u) [Group L] : Subgroup (MulAut L) :=
  (MulAut.conj : L →* MulAut L).range

instance innerAutomorphismSubgroup_normal (L : Type u) [Group L] :
    (innerAutomorphismSubgroup L).Normal := by
  constructor
  intro f hf a
  obtain ⟨l, rfl⟩ := hf
  refine ⟨a l, ?_⟩
  ext x
  change a l * x * (a l)⁻¹ = a (l * a.symm x * l⁻¹)
  simp

@[expose] def outerAutomorphismGroup (L : Type u) [Group L] :=
  MulAut L ⧸ innerAutomorphismSubgroup L

instance outerAutomorphismGroup_group (L : Type u) [Group L] :
    Group (outerAutomorphismGroup L) :=
  inferInstanceAs (Group (MulAut L ⧸ innerAutomorphismSubgroup L))

@[expose] def outerAutomorphismMap (L : Type u) [Group L] :
    MulAut L →* outerAutomorphismGroup L :=
  QuotientGroup.mk' (innerAutomorphismSubgroup L)

theorem outerAutomorphismMap_ker (L : Type u) [Group L] :
    (outerAutomorphismMap L).ker = innerAutomorphismSubgroup L := by
  exact QuotientGroup.ker_mk' (innerAutomorphismSubgroup L)

theorem automorphism_subgroup_isSolvable
    (L : Type u) [Group L] (A : Subgroup (MulAut L))
    [Group.IsSolvable (outerAutomorphismGroup L)]
    [Group.IsSolvable ((innerAutomorphismSubgroup L).subgroupOf A)] :
    Group.IsSolvable A := by
  apply Group.isSolvable_of_ker_le_range
    ((innerAutomorphismSubgroup L).subgroupOf A).subtype
    ((outerAutomorphismMap L).comp A.subtype)
  intro a ha
  refine ⟨⟨a, ?_⟩, rfl⟩
  change (a : MulAut L) ∈ innerAutomorphismSubgroup L
  have ha' : (a : MulAut L) ∈ (outerAutomorphismMap L).ker := ha
  rwa [outerAutomorphismMap_ker] at ha'

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
