module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticLinearIdentities

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem quadratic_pair_eigenvector_span_invariant {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (first second : space ≃ₗ[field] space)
    (hfirst : ((first : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hsecond : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (member : space) (eigenvalue : field) (hne : eigenvalue ≠ 0)
    (heigenvector : second (first member) = eigenvalue • member) :
    ∀ element ∈ Submodule.span field {member, first member},
      first element ∈ Submodule.span field {member, first member} ∧
      second element ∈ Submodule.span field {member, first member} := by
  let span := Submodule.span field {member, first member}
  have hmember : member ∈ span := Submodule.subset_span (Set.mem_insert _ _)
  have hfirstMember : first member ∈ span := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hfirstSquare : first (first member) ∈ span := by
    rw [quadratic_linear_square_apply first hfirst]
    exact span.sub_mem (span.add_mem hfirstMember hfirstMember) hmember
  have hsecondFirst : second (first member) ∈ span := by
    rw [heigenvector]
    exact span.smul_mem eigenvalue hmember
  have hsecondMember : second member ∈ span := by
    have heq : first member = eigenvalue • second.symm member := by
      have hpreimage := congrArg second.symm heigenvector
      rw [second.symm_apply_apply, map_smul] at hpreimage
      exact hpreimage
    have hinverse : second.symm member = eigenvalue⁻¹ • first member := by
      rw [heq, inv_smul_smul₀ hne]
    have hformula : second member = member + member - eigenvalue⁻¹ • first member := by
      have heq := quadratic_linear_inverse_apply second hsecond member
      rw [hinverse] at heq
      have hrewritten := (eq_sub_iff_add_eq).mp heq
      calc
        second member = (eigenvalue⁻¹ • first member + second member) - eigenvalue⁻¹ • first member := by abel
        _ = member + member - eigenvalue⁻¹ • first member := by rw [hrewritten]
    rw [hformula]
    exact span.sub_mem (span.add_mem hmember hmember) (span.smul_mem _ hfirstMember)
  intro element helement
  obtain ⟨firstScalar, secondScalar, rfl⟩ := Submodule.mem_span_pair.mp helement
  constructor
  · rw [map_add, map_smul, map_smul]
    exact span.add_mem (span.smul_mem _ hfirstMember) (span.smul_mem _ hfirstSquare)
  · rw [map_add, map_smul, map_smul]
    exact span.add_mem (span.smul_mem _ hsecondMember) (span.smul_mem _ hsecondFirst)

theorem quadratic_pair_has_nonzero_invariant_span {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] [Nontrivial space]
    (first second : space ≃ₗ[field] space)
    (hfirst : ((first : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hsecond : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0) :
    ∃ member : space, member ≠ 0 ∧
      ∀ element ∈ Submodule.span field {member, first member},
        first element ∈ Submodule.span field {member, first member} ∧
        second element ∈ Submodule.span field {member, first member} := by
  obtain ⟨eigenvalue, heigenvalue⟩ :=
    Module.End.exists_eigenvalue ((second * first : space ≃ₗ[field] space) : Module.End field space)
  obtain ⟨member, heigenvector⟩ := heigenvalue.exists_hasEigenvector
  have hmemberNe := (Module.End.hasEigenvector_iff.mp heigenvector).2
  have heq : second (first member) = eigenvalue • member := heigenvector.apply_eq_smul
  have heigenvalueNe : eigenvalue ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at heq
    have hfirstZero : first member = 0 := second.injective (heq.trans (map_zero second).symm)
    exact hmemberNe (first.injective (hfirstZero.trans (map_zero first).symm))
  exact ⟨member, hmemberNe,
    quadratic_pair_eigenvector_span_invariant first second hfirst hsecond member eigenvalue heigenvalueNe heq⟩

end CFSG.RankThreeEvenClassification.Helpers
