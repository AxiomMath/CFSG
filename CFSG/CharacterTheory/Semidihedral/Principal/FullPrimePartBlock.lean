module

public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterValueIntegrality
public import CFSG.CharacterTheory.TwoRankLowerBound.PrimePrimaryFactorization

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem degree_div_card_mem_localizedComplexIntegerRing (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (data : FiniteComplexRepresentation G)
    (hdegree : p ^ (Nat.card G).factorization p ∣ Module.finrank ℂ data.vector) :
    data.character 1 / (Nat.card G : ℂ) ∈ localizedComplexIntegerRing ideal := by
  have hp : p.Prime := Fact.out
  obtain ⟨d, hd⟩ := hdegree
  have hcoprime : Nat.Coprime p (Nat.card G / p ^ (Nat.card G).factorization p) :=
    Nat.coprime_ordCompl hp Nat.card_pos.ne'
  have hcard : ((Nat.card G : ℕ) : ℂ) = ((p ^ (Nat.card G).factorization p : ℕ) : ℂ) *
      ((Nat.card G / p ^ (Nat.card G).factorization p : ℕ) : ℂ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  have hnotmem : ((Nat.card G / p ^ (Nat.card G).factorization p : ℕ) :
      ComplexAlgebraicIntegers) ∉ ideal := by
    intro hmem
    have hzero : ((Nat.card G / p ^ (Nat.card G).factorization p : ℕ) :
        ComplexAlgebraicIntegers ⧸ ideal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk ideal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) p] at hzero
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hcoprime hzero)
  rw [localizedComplexIntegerRing_mem_iff_fraction]
  refine ⟨(d : ComplexAlgebraicIntegers), _, hnotmem, ?_⟩
  have hpow : ((p ^ (Nat.card G).factorization p : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  rw [FiniteComplexRepresentation.character, Representation.char_one, hd, hcard, Nat.cast_mul,
    mul_div_mul_left _ _ hpow]
  push_cast
  rfl

theorem singleton_admissible_of_full_prime_part_dvd_degree
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (χ : basis.index)
    (hdegree : p ^ (Nat.card G).factorization p ∣
      Module.finrank ℂ (basis.representation χ).vector) :
    characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) {χ} := by
  change ∀ g : G, (characterSubsetIdempotent basis {χ}).coeff g ∈
    localizedComplexIntegerRing ideal
  intro g
  rw [characterSubsetIdempotent_coeff, Finset.sum_singleton]
  exact (localizedComplexIntegerRing ideal).mul_mem
    (degree_div_card_mem_localizedComplexIntegerRing ideal p _ hdegree)
    (complexAlgebraicInteger_mem_localized_ring ideal
      ⟨_, (mem_integralClosure_iff ℤ ℂ).mpr (finite_character_value_isIntegral _ g⁻¹)⟩)

theorem full_prime_part_character_degree_singleton_block_singular_vanishing
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (χ : basis.index)
    (hdegree : p ^ (Nat.card G).factorization p ∣
      Module.finrank ℂ (basis.representation χ).vector) :
    coefficientBlock basis (localizedComplexIntegerRing ideal) χ = {χ} ∧
      ∀ g : G, p ∣ orderOf g → (basis.representation χ).character g = 0 := by
  have hadmissible := singleton_admissible_of_full_prime_part_dvd_degree basis ideal p χ hdegree
  have hblock : coefficientBlock basis (localizedComplexIntegerRing ideal) χ = {χ} :=
    Finset.Subset.antisymm
      (coefficientBlock_subset_admissible basis _ {χ} hadmissible χ (Finset.mem_singleton_self χ))
      (Finset.singleton_subset_iff.mpr (coefficientBlock_self_mem basis _ χ))
  refine ⟨hblock, fun g hg => ?_⟩
  have hp : p.Prime := Fact.out
  obtain ⟨a, b, e, -, -, hcommute, hproduct, hprimary, hregular⟩ :=
    finite_prime_primary_factorization g p hp
  have hnontrivial : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at hproduct
    subst hproduct
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hregular hg)
  have horthogonal := coefficientBlock_section_column_orthogonality basis ideal p χ a 1 b 1 e 0
    hprimary (by simp) hregular (by simp) hcommute (Commute.one_left 1)
    (fun hconj => hnontrivial (isConj_one_left.mp hconj))
  simp only [hblock, Finset.sum_singleton, hproduct, mul_one, inv_one] at horthogonal
  exact (mul_eq_zero.mp horthogonal).resolve_right
    (irreducible_character_degree_ne_zero _ (basis.irreducible χ))

end CFSG.Semidihedral.Principal
