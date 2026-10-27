module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticEigenvectorSpan

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem linear_invariant_submodule_map_eq {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [FiniteDimensional field space]
    (automorphism : space ≃ₗ[field] space) (subspace : Submodule field space)
    (hinvariant : ∀ member ∈ subspace, automorphism member ∈ subspace) :
    subspace.map (automorphism : Module.End field space) = subspace := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro member ⟨preimage, hpreimage, rfl⟩
    exact hinvariant preimage hpreimage
  · rw [LinearEquiv.finrank_map_eq]

theorem quadratic_pair_irreducible_dimension {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] [Nontrivial space]
    (first second : space ≃ₗ[field] space)
    (hfirst : ((first : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hsecond : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hirreducible : ∀ subspace : Submodule field space,
      subspace.map (first : Module.End field space) = subspace →
      subspace.map (second : Module.End field space) = subspace →
      subspace = ⊥ ∨ subspace = ⊤) : Module.finrank field space ≤ 2 := by
  classical
  obtain ⟨member, hmemberNe, hinvariant⟩ :=
    quadratic_pair_has_nonzero_invariant_span first second hfirst hsecond
  let span := Submodule.span field {member, first member}
  have hfirstMap := linear_invariant_submodule_map_eq first span
    (fun element helement => (hinvariant element helement).1)
  have hsecondMap := linear_invariant_submodule_map_eq second span
    (fun element helement => (hinvariant element helement).2)
  have hspanNe : span ≠ ⊥ := by
    intro heq
    have hmem : member ∈ span := Submodule.subset_span (Set.mem_insert _ _)
    rw [heq, Submodule.mem_bot] at hmem
    exact hmemberNe hmem
  have hspanTop : span = ⊤ := (hirreducible span hfirstMap hsecondMap).resolve_left hspanNe
  have hbound := finrank_span_le_card (R := field) {member, first member}
  have hcardBound : ({member, first member} : Set space).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    simpa only [Finset.card_singleton] using Finset.card_insert_le member {first member}
  change Module.finrank field span ≤ _ at hbound
  rw [hspanTop, finrank_top] at hbound
  exact hbound.trans hcardBound

end CFSG.RankThreeEvenClassification.Helpers
