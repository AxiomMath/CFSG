module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.IdempotentTwist
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassCoefficients
public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue
public import CFSG.Open.LocalVocabulary

public noncomputable section

open scoped Classical Pointwise

namespace CFSG.BrauerCharacters

open CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers
open CFSG.BlockSectionOrthogonality.Helpers

variable {ideal : Ideal ComplexAlgebraicIntegers} [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]

omit [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] in
theorem exists_coeff_not_mem_of_centralChar_not_mem {L : Type} [Group L] [Fintype L]
    {ψ : L → ℂ} (hψ : ψ ∈ CFSG.BlocksIrr L) {f : L → ℂ} (hf : CFSG.BlocksIsCentralR ideal f)
    (hfψ : CFSG.BlocksCentralChar ψ f ∉ CFSG.BlocksLocalMaxIdeal ideal) :
    ∃ y : L, f y ∉ CFSG.BlocksLocalMaxIdeal ideal ∧
      CFSG.BlocksCentralChar ψ (classCoefficients (ConjClasses.mk y)) ∉
        CFSG.BlocksLocalMaxIdeal ideal := by
  have hm : ideal.IsMaximal := inferInstance
  let : Fintype (ConjClasses L) := Fintype.ofFinite _
  have hexp := central_class_expansion f hf.2 (fun Y => Quotient.out Y)
    (fun Y => Quotient.out_eq Y)
  rw [finsum_eq_sum_of_fintype] at hexp
  rw [hexp, centralChar_sum] at hfψ
  by_contra hnot
  push Not at hnot
  apply hfψ
  apply localMaxIdeal_sum ideal hm
  intro Y _
  rw [centralChar_smul]
  by_cases hY : f (Quotient.out Y) ∈ CFSG.BlocksLocalMaxIdeal ideal
  · exact localMaxIdeal_mul_localRing ideal hm hY
      (centralChar_localRing ideal hm hψ (classCoefficients_central ideal hm Y))
  · have h := hnot _ hY
    rw [show ConjClasses.mk (Quotient.out Y) = Y from Quotient.out_eq Y] at h
    rw [mul_comm]
    exact localMaxIdeal_mul_localRing ideal hm h (hf.1 _)

end CFSG.BrauerCharacters
