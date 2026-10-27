module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterSubsetProjection
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def primeSectionUnion {G : Type*} [Group G] (prime : ℕ) (domain : Set G) : Prop :=
  ∀ (leftPrimary rightPrimary leftRegular rightRegular : G) (leftExponent rightExponent : ℕ),
    orderOf leftPrimary ∣ prime ^ leftExponent → orderOf rightPrimary ∣ prime ^ rightExponent →
    Nat.Coprime prime (orderOf leftRegular) → Nat.Coprime prime (orderOf rightRegular) →
    Commute leftPrimary leftRegular → Commute rightPrimary rightRegular →
    IsConj leftPrimary rightPrimary →
    (leftPrimary * leftRegular ∈ domain ↔ rightPrimary * rightRegular ∈ domain)

theorem admissible_characterSubsetColumnKernel_zero_across_sections
    {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) support)
    (domain : Set G) (hsections : primeSectionUnion prime domain)
    (left right : G) (hmixed : ¬ (left ∈ domain ↔ right ∈ domain)) :
    characterSubsetColumnKernel basis support left right = 0 := by
  obtain ⟨leftPrimary, leftRegular, leftExponent, _, _, hleftCommute, hleftProduct,
    hleftPrimary, hleftRegular⟩ := finite_prime_primary_factorization left prime Fact.out
  obtain ⟨rightPrimary, rightRegular, rightExponent, _, _, hrightCommute, hrightProduct,
    hrightPrimary, hrightRegular⟩ := finite_prime_primary_factorization right prime Fact.out
  have hnotconjugate : ¬ IsConj leftPrimary rightPrimary := by
    intro hconjugate
    apply hmixed
    rw [← hleftProduct, ← hrightProduct]
    exact hsections leftPrimary rightPrimary leftRegular rightRegular leftExponent rightExponent
      hleftPrimary hrightPrimary hleftRegular hrightRegular hleftCommute hrightCommute hconjugate
  rw [← hleftProduct, ← hrightProduct]
  exact admissible_character_section_column_orthogonality basis ideal prime support hadmissible
    leftPrimary rightPrimary leftRegular rightRegular leftExponent rightExponent
    hleftPrimary hrightPrimary hleftRegular hrightRegular hleftCommute hrightCommute hnotconjugate

theorem admissible_characterSubsetProjection_section_mask_commute
    {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) support)
    (domain : Set G) (hsections : primeSectionUnion prime domain) (function : G → ℂ) :
    characterSubsetProjection basis support (characterFunctionMask domain function) =
      characterFunctionMask domain (characterSubsetProjection basis support function) :=
  characterSubsetProjection_mask_commute basis support domain
    (admissible_characterSubsetColumnKernel_zero_across_sections basis ideal prime support
      hadmissible domain hsections) function

theorem admissible_coefficientCharacterSpace_section_mask_mem
    {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) support)
    (domain : Set G) (hsections : primeSectionUnion prime domain)
    (function : G → ℂ) (hfunction : function ∈ coefficientCharacterSpace basis support) :
    characterFunctionMask domain function ∈ coefficientCharacterSpace basis support :=
  coefficientCharacterSpace_mask_mem basis support domain
    (admissible_characterSubsetColumnKernel_zero_across_sections basis ideal prime support
      hadmissible domain hsections) function hfunction

theorem coefficientBlock_section_mask_commute {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (blockLabel : basis.index)
    (domain : Set G) (hsections : primeSectionUnion prime domain) (function : G → ℂ) :
    characterSubsetProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel)
        (characterFunctionMask domain function) =
      characterFunctionMask domain
        (characterSubsetProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel)
          function) :=
  admissible_characterSubsetProjection_section_mask_commute basis ideal prime _
    (coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) blockLabel)
    domain hsections function

theorem coefficientBlock_section_mask_mem {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (blockLabel : basis.index)
    (domain : Set G) (hsections : primeSectionUnion prime domain) (function : G → ℂ)
    (hfunction : function ∈
      coefficientCharacterSpace basis (coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel)) :
    characterFunctionMask domain function ∈
      coefficientCharacterSpace basis (coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel) :=
  admissible_coefficientCharacterSpace_section_mask_mem basis ideal prime _
    (coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) blockLabel)
    domain hsections function hfunction

end CFSG.TwoRankLowerBound.Helpers
