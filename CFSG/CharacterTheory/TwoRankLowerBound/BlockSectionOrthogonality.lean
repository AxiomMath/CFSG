module

public import CFSG.CharacterTheory.TwoRankLowerBound.LocalizedAlgebraicIntegers
public import CFSG.CharacterTheory.TwoRankLowerBound.CoefficientBlocks
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedSectionTrace

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem localizedComplexIntegerRing_residue_charP (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] :
    CharP (IsLocalRing.ResidueField (localizedComplexIntegerRing ideal)) prime := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : prime.Prime)).mpr
  have hnotunit : ¬ IsUnit (prime : localizedComplexIntegerRing ideal) := by
    intro hunit
    have hresidue := (localizedComplexIntegerResidue_isUnit_iff ideal _).mp hunit
    rw [map_natCast] at hresidue
    exact hresidue (CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) prime prime |>.mpr (dvd_refl prime))
  have hzero : IsLocalRing.residue (localizedComplexIntegerRing ideal)
      (prime : localizedComplexIntegerRing ideal) = 0 := by
    exact Classical.not_not.mp
      (mt (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hnotunit)
  simpa only [map_natCast] using hzero

theorem rootOfUnity_mem_localizedComplexIntegerRing (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsPrime] (period : ℕ) (hpositive : 0 < period) (root : ℂ) (hroot : root ^ period = 1) :
    root ∈ localizedComplexIntegerRing ideal :=
  complexAlgebraicInteger_mem_localized_ring ideal
    ⟨root, rootOfUnity_mem_complexAlgebraicIntegers root period hpositive hroot⟩

theorem admissible_character_section_column_orthogonality {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) support)
    (leftPrimary rightPrimary leftRegular rightRegular : group) (leftExponent rightExponent : ℕ)
    (hleftPrimary : orderOf leftPrimary ∣ prime ^ leftExponent)
    (hrightPrimary : orderOf rightPrimary ∣ prime ^ rightExponent)
    (hleftRegular : Nat.Coprime prime (orderOf leftRegular))
    (hrightRegular : Nat.Coprime prime (orderOf rightRegular))
    (hleftCommute : Commute leftPrimary leftRegular) (hrightCommute : Commute rightPrimary rightRegular)
    (hnotconjugate : ¬ IsConj leftPrimary rightPrimary) :
    (∑ label ∈ support, (basis.representation label).character (leftPrimary * leftRegular) *
      (basis.representation label).character (rightPrimary * rightRegular)⁻¹) = 0 := by
  let := localizedComplexIntegerRing_residue_charP ideal prime
  rw [← characterSubsetIdempotent_twoSided_trace]
  exact complex_local_central_idempotent_section_trace_zero (localizedComplexIntegerRing ideal) prime
    (characterSubsetIdempotent basis support) hadmissible
    (characterIdempotentExpansion_central basis _) (characterSubsetIdempotent_isIdempotent basis support)
    leftPrimary rightPrimary leftRegular rightRegular leftExponent rightExponent
    hleftPrimary hrightPrimary hleftRegular hrightRegular hleftCommute hrightCommute hnotconjugate
    (rootOfUnity_mem_localizedComplexIntegerRing ideal _
      (Nat.mul_pos (orderOf_pos leftRegular) (orderOf_pos rightRegular)))

theorem coefficientBlock_section_column_orthogonality {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (blockLabel : basis.index)
    (leftPrimary rightPrimary leftRegular rightRegular : group) (leftExponent rightExponent : ℕ)
    (hleftPrimary : orderOf leftPrimary ∣ prime ^ leftExponent)
    (hrightPrimary : orderOf rightPrimary ∣ prime ^ rightExponent)
    (hleftRegular : Nat.Coprime prime (orderOf leftRegular))
    (hrightRegular : Nat.Coprime prime (orderOf rightRegular))
    (hleftCommute : Commute leftPrimary leftRegular) (hrightCommute : Commute rightPrimary rightRegular)
    (hnotconjugate : ¬ IsConj leftPrimary rightPrimary) :
    (∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
      (basis.representation label).character (leftPrimary * leftRegular) *
        (basis.representation label).character (rightPrimary * rightRegular)⁻¹) = 0 :=
  admissible_character_section_column_orthogonality basis ideal prime _
    (coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) blockLabel)
    leftPrimary rightPrimary leftRegular rightRegular leftExponent rightExponent
    hleftPrimary hrightPrimary hleftRegular hrightRegular hleftCommute hrightCommute hnotconjugate

end CFSG.TwoRankLowerBound.Helpers
