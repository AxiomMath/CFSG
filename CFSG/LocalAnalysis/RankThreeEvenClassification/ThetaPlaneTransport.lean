module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneQuotient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem card_join_of_commuting_subgroups_le {G : Type u} [Group G] [Finite G]
    (first second : Subgroup G)
    (hcommute : ∀ left ∈ first, ∀ right ∈ second, Commute left right) :
    Nat.card (first ⊔ second : Subgroup G) ≤ Nat.card first * Nat.card second := by
  let productHom := first.subtype.noncommCoprod second.subtype
    (fun left right => hcommute left left.property right right.property)
  have hrange : productHom.range = first ⊔ second := by
    apply le_antisymm
    · rintro element ⟨⟨left, right⟩, rfl⟩
      exact Subgroup.mul_mem_sup left.property right.property
    · apply sup_le
      · intro element helement
        refine ⟨(⟨element, helement⟩, 1), ?_⟩
        change element * (1 : G) = element
        exact mul_one element
      · intro element helement
        refine ⟨(1, ⟨element, helement⟩), ?_⟩
        change (1 : G) * element = element
        exact one_mul element
  rw [← hrange, ← Nat.card_prod]
  exact Nat.card_le_card_of_surjective productHom.rangeRestrict
    (MonoidHom.rangeRestrict_surjective productHom)

theorem thetaPlaneIntersection_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* H) (plane : Subgroup G) :
    (thetaPlaneIntersection prime plane).map equivalence.toMonoidHom =
      thetaPlaneIntersection prime (plane.map equivalence.toMonoidHom) := by
  have hcentral : equivalence.toMonoidHom.ker ≤ Subgroup.center G := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact bot_le
  have hkernel : IsPGroup prime equivalence.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact IsPGroup.of_bot
  have hsymmCentral : equivalence.symm.toMonoidHom.ker ≤ Subgroup.center H := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact bot_le
  have hsymmKernel : IsPGroup prime equivalence.symm.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact IsPGroup.of_bot
  apply le_antisymm
  · exact thetaPlaneIntersection_map_le_of_central_pKernel prime hprime equivalence.toMonoidHom
      equivalence.surjective hcentral hkernel plane
  · apply (Subgroup.map_le_map_iff_of_injective (f := equivalence.symm.toMonoidHom)
      equivalence.symm.injective).mp
    rw [subgroup_map_equiv_symm]
    have hle := thetaPlaneIntersection_map_le_of_central_pKernel prime hprime equivalence.symm.toMonoidHom
      equivalence.symm.surjective hsymmCentral hsymmKernel (plane.map equivalence.toMonoidHom)
    simpa only [subgroup_map_equiv_symm] using hle

theorem thetaPlaneCommutators_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* H) (plane : Subgroup G) :
    (thetaPlaneCommutators prime plane).map equivalence.toMonoidHom =
      thetaPlaneCommutators prime (plane.map equivalence.toMonoidHom) := by
  have hcentral : equivalence.toMonoidHom.ker ≤ Subgroup.center G := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact bot_le
  have hkernel : IsPGroup prime equivalence.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact IsPGroup.of_bot
  have hsymmCentral : equivalence.symm.toMonoidHom.ker ≤ Subgroup.center H := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact bot_le
  have hsymmKernel : IsPGroup prime equivalence.symm.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact IsPGroup.of_bot
  apply le_antisymm
  · exact thetaPlaneCommutators_map_le_of_central_pKernel prime hprime equivalence.toMonoidHom
      equivalence.surjective hcentral hkernel plane equivalence.injective.injOn
  · apply (Subgroup.map_le_map_iff_of_injective (f := equivalence.symm.toMonoidHom)
      equivalence.symm.injective).mp
    rw [subgroup_map_equiv_symm]
    have hle := thetaPlaneCommutators_map_le_of_central_pKernel prime hprime equivalence.symm.toMonoidHom
      equivalence.symm.surjective hsymmCentral hsymmKernel (plane.map equivalence.toMonoidHom)
      equivalence.symm.injective.injOn
    simpa only [subgroup_map_equiv_symm] using hle

theorem thetaPlaneAlpha_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* H) (plane : Subgroup G) :
    (thetaPlaneAlpha prime plane).map equivalence.toMonoidHom =
      thetaPlaneAlpha prime (plane.map equivalence.toMonoidHom) := by
  rw [thetaPlaneAlpha, Subgroup.map_sup, thetaPlaneCommutators_map_equiv prime hprime,
    thetaPlaneIntersection_map_equiv prime hprime]
  rfl

theorem normalizer_plane_le_normalizer_alpha {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) :
    Subgroup.normalizer (plane : Set G) ≤ Subgroup.normalizer (thetaPlaneAlpha prime plane : Set G) := by
  intro element helement
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (thetaPlaneAlpha prime plane).map (MulAut.conj element).toMonoidHom = thetaPlaneAlpha prime plane
  rw [thetaPlaneAlpha_map_equiv prime hprime (MulAut.conj element)]
  have hplane : plane.map (MulAut.conj element).toMonoidHom = plane :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp helement
  rw [hplane]

end CFSG.RankThreeEvenClassification.Helpers
