module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitBound

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit

open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem familyStabilizer_eq_top_of_card_one (H : Subgroup G)
    (hO : Nat.card (FamilyOrbit H) = 1) : familyStabilizer H = ⊤ := by
  let _ := (Nat.card_eq_one_iff_unique.mp hO).1
  apply le_antisymm le_top
  intro alpha _
  exact congrArg Subtype.val
    (Subsingleton.elim (alpha • familyOrbitBase H) (familyOrbitBase H))

theorem familyOuterHom_surjective_of_card_one (H : Subgroup G)
    (hO : Nat.card (FamilyOrbit H) = 1) : Function.Surjective (familyOuterHom H) := by
  intro x
  obtain ⟨alpha, rfl⟩ := QuotientGroup.mk'_surjective (OuterAutomorphisms.inner G) x
  have halpha : alpha ∈ familyStabilizer H := by
    rw [familyStabilizer_eq_top_of_card_one H hO]
    exact Subgroup.mem_top alpha
  exact ⟨(QuotientGroup.mk' (familyInner H)) ⟨alpha, halpha⟩, rfl⟩

@[expose] noncomputable def singletonFamilyOuterEquiv (H : Subgroup G)
    (hO : Nat.card (FamilyOrbit H) = 1) : FamilyOuter H ≃* OuterAutomorphisms.Outer G :=
  MulEquiv.ofBijective (familyOuterHom H)
    ⟨familyOuterHom_injective H, familyOuterHom_surjective_of_card_one H hO⟩

theorem singletonFamilyOuterEquiv_mk (H : Subgroup G)
    (hO : Nat.card (FamilyOrbit H) = 1) (alpha : familyStabilizer H) :
    singletonFamilyOuterEquiv H hO ((QuotientGroup.mk' (familyInner H)) alpha) =
      (QuotientGroup.mk' (OuterAutomorphisms.inner G)) alpha.val := rfl

theorem orthogonal_geometry_small_family_orbit_solvability [Finite G]
    (H : Subgroup G) (d : Nat) (hA : derivedSeries (FamilyOuter H) d = ⊥)
    (hO : Nat.card (FamilyOrbit H) ≤ 3) :
    derivedSeries (OuterAutomorphisms.Outer G) (d + 2) = ⊥ := by
  simpa only [Nat.add_comm] using
    derived_bound_of_kernel_le_range (kernelOuterHom H) (outerOrbitAction H)
      (outerOrbitAction_kernel_eq_range H).le d 2
      (kernelOuter_derived_eq_bot H d hA)
      (symmetric_second_derived_eq_bot (FamilyOrbit H) hO)

theorem orthogonal_geometry_singleton_family_orbit_solvability [Finite G]
    (H : Subgroup G) (d : Nat) (hA : derivedSeries (FamilyOuter H) d = ⊥)
    (hO : Nat.card (FamilyOrbit H) = 1) :
    derivedSeries (OuterAutomorphisms.Outer G) d = ⊥ := by
  rw [← map_derivedSeries_eq (singletonFamilyOuterEquiv H hO).surjective d, hA,
    Subgroup.map_bot]

end CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
