module

public import CFSG.CharacterTheory.BlockSectionOrthogonality
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.BlockBasics.Defects
public import CFSG.CharacterTheory.TwoRankLowerBound.PrimePrimaryFactorization
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

open scoped Classical ComplexConjugate

namespace CFSG.Wreathed.BrauerWreathedOrder

open CFSG CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G]

theorem isPPart_one_of_odd {z : G} (hz : Odd (orderOf z)) : BlocksIsPPart 2 z 1 :=
  ⟨z, one_mul z, mul_one z, ⟨0, by simp⟩, orderOf_pos z,
    Nat.coprime_two_right.mpr hz⟩

theorem exists_isPPart_ne_one {u : G} (hu : ¬ Odd (orderOf u)) :
    ∃ u₂ : G, BlocksIsPPart 2 u u₂ ∧ u₂ ≠ 1 := by
  obtain ⟨a, b, e, -, -, hab, hprod, hord, hcop⟩ :=
    CFSG.TwoRankLowerBound.Helpers.finite_prime_primary_factorization u 2 Nat.prime_two
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  refine ⟨a, ⟨b, hprod, by rw [← hab.eq]; exact hprod, ⟨k, hk⟩, orderOf_pos b, hcop.symm⟩, ?_⟩
  rintro rfl
  apply hu
  rw [one_mul] at hprod
  rw [← hprod]
  exact Nat.coprime_two_left.mp hcop

theorem sum_principal_character_mul_conj_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {u z : G}
    (hu : ¬ Odd (orderOf u)) (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u * conj ((basis.representation χ).character z) = 0 := by
  have hm : ideal.IsMaximal := inferInstance
  obtain ⟨u₂, hu₂, hu₂1⟩ := exists_isPPart_ne_one hu
  have hnc : ¬ IsConj u₂ 1 := fun h => hu₂1 (isConj_one_left.mp h)
  have hB : BlocksIsBlock ideal G
      (BlocksBlockOf ideal G (basis.representation principal).character) :=
    ⟨_, CFSG.BlockBasics.basis_character_mem_irr basis principal, rfl⟩
  have h := CFSG.BlockSectionOrthogonality.block_section_orthogonality 2 Nat.prime_two ideal hm
    (CFSG.BlockBasics.prime_mem_of_charP 2 ideal) G _ hB u z u₂ 1 hu₂ (isPPart_one_of_odd hz) hnc
  rw [← CFSG.BlockBasics.coefficientBlock_image basis ideal principal] at h
  have hinj : Set.InjOn (fun l => (basis.representation l).character)
      ((coefficientBlock basis (localizedComplexIntegerRing ideal) principal : Finset _) :
        Set basis.index) := fun l _ l' _ hll' => basis.distinct hll'
  rw [finsum_mem_image hinj, finsum_mem_coe_finset] at h
  exact h

theorem sum_principal_combination_mul_conj_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {ι : Type*}
    (s : Finset ι) (w : ι → G) (hw : ∀ i ∈ s, ¬ Odd (orderOf (w i))) (coeff : ι → ℂ)
    (c : basis.index → ℂ)
    (hc : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      c χ = ∑ i ∈ s, coeff i * (basis.representation χ).character (w i))
    {z : G} (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      c χ * conj ((basis.representation χ).character z) = 0 := by
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hc χ hχ, Finset.sum_mul], Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.sum_congr rfl fun χ _ => mul_assoc _ _ _, ← Finset.mul_sum,
    sum_principal_character_mul_conj_eq_zero basis ideal principal (hw i hi) hz, mul_zero]

end CFSG.Wreathed.BrauerWreathedOrder
