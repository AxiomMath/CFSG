module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralIdempotentSpectral
public import CFSG.CharacterTheory.TwoRankLowerBound.ConjugacyAverageCharacter

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def groupAlgebraTwoSidedOperator {ring group : Type*} [CommRing ring] [Group group]
    (coefficient : MonoidAlgebra ring group) (left right : group) : Module.End ring (MonoidAlgebra ring group) :=
  Algebra.lmul ring (MonoidAlgebra ring group) coefficient *
    Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single left 1) *
      LinearMap.mulRight ring (MonoidAlgebra.single right⁻¹ 1)

theorem groupAlgebraTwoSidedOperator_trace {ring group : Type*} [CommRing ring] [Group group] [Fintype group]
    (coefficient : MonoidAlgebra ring group) (left right : group) :
    LinearMap.trace ring (MonoidAlgebra ring group) (groupAlgebraTwoSidedOperator coefficient left right) =
      ∑ element : group, coefficient.coeff (element * right * element⁻¹ * left⁻¹) := by
  rw [LinearMap.trace_eq_matrix_trace ring (MonoidAlgebra.basis group ring), Matrix.trace]
  change (∑ element : group, LinearMap.toMatrix (MonoidAlgebra.basis group ring)
    (MonoidAlgebra.basis group ring) (groupAlgebraTwoSidedOperator coefficient left right) element element) = _
  apply Finset.sum_congr rfl
  intro element _
  rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
  change (coefficient * (MonoidAlgebra.single left 1 *
    (MonoidAlgebra.single element 1 * MonoidAlgebra.single right⁻¹ 1))).coeff element = _
  simp only [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_mul_single_apply, mul_one]
  congr 1
  group

theorem complexCharacterIdempotent_twoSided_trace {group : Type*} [Group group] [Fintype group]
    (data : FiniteComplexRepresentation group) (hirreducible : data.IsIrreducible) (left right : group) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ group)
      (groupAlgebraTwoSidedOperator (complexCharacterIdempotent data.character) left right) =
      data.character left * data.character right⁻¹ := by
  rw [groupAlgebraTwoSidedOperator_trace]
  simp only [complexCharacterIdempotent_coeff]
  have hinverse : ∀ element : group,
      (element * right * element⁻¹ * left⁻¹)⁻¹ = left * (element * right⁻¹ * element⁻¹) := by
    intro element
    group
  simp only [hinverse]
  rw [← Finset.mul_sum, irreducible_conjugacyAverage_character data hirreducible]
  have hcard : (Nat.card group : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card group ≠ 0)
  have hdegree := irreducible_character_degree_ne_zero data hirreducible
  field_simp

theorem characterSubsetIdempotent_coeff {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index) (element : group) :
    (characterSubsetIdempotent basis support).coeff element =
      ∑ label ∈ support, ((basis.representation label).character 1 / (Nat.card group : ℂ)) *
        (basis.representation label).character element⁻¹ := by
  simp only [characterSubsetIdempotent, characterIdempotentExpansion, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, complexCharacterIdempotent_coeff]
  simpa only [ite_mul, one_mul, zero_mul] using
    Finset.sum_ite_mem_eq support (fun label =>
      ((basis.representation label).character 1 / (Nat.card group : ℂ)) *
        (basis.representation label).character element⁻¹)

theorem characterSubsetIdempotent_twoSided_trace {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index) (left right : group) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ group)
      (groupAlgebraTwoSidedOperator (characterSubsetIdempotent basis support) left right) =
      ∑ label ∈ support, (basis.representation label).character left *
        (basis.representation label).character right⁻¹ := by
  rw [groupAlgebraTwoSidedOperator_trace]
  simp only [characterSubsetIdempotent_coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro label _
  rw [← complexCharacterIdempotent_twoSided_trace (basis.representation label) (basis.irreducible label),
    groupAlgebraTwoSidedOperator_trace]
  simp only [complexCharacterIdempotent_coeff]

end CFSG.TwoRankLowerBound.Helpers
