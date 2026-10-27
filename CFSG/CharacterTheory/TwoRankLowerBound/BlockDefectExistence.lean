module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterResidueCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.ClassProductDefect

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem conjugacyClassSum_one {ring group : Type*} [CommRing ring] [Group group] [Fintype group] :
    conjugacyClassSum (ring := ring) (ConjClasses.mk (1 : group)) = 1 := by
  ext element
  rw [conjugacyClassSum_coeff]
  change (if ConjClasses.mk element = ConjClasses.mk (1 : group) then (1 : ring) else 0) =
    (MonoidAlgebra.single (1 : group) (1 : ring)).coeff element
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hequal : ConjClasses.mk element = ConjClasses.mk (1 : group) ↔ element = 1 :=
    ConjClasses.mk_eq_mk_iff_isConj.trans isConj_one_left
  simp [hequal, eq_comm]

theorem centralConjugacyClassSum_one {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) : centralConjugacyClassSum ring (ConjClasses.mk (1 : group)) = 1 :=
  Subtype.ext conjugacyClassSum_one

theorem centralCharacterResidueHom_class_product {group : Type*} [Group group] [Fintype group]
    [Fintype (ConjClasses group)] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (label : basis.index)
    (left right : ConjClasses group) :
    centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ left) *
        centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ right) =
      ∑ result : ConjClasses group,
        (classProductCoefficient left right (conjugacyClassRepresentative result) :
          ComplexAlgebraicIntegers ⧸ ideal) *
          centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ result) := by
  rw [← map_mul, centralCharacterResidueHom_class_expansion]
  apply Finset.sum_congr rfl
  intro result _
  have hcoordinate : centralConjugacyClassCoefficient (localizedComplexIntegerRing ideal)
      (centralConjugacyClassSum _ left * centralConjugacyClassSum _ right) result =
        (classProductCoefficient left right (conjugacyClassRepresentative result) :
          localizedComplexIntegerRing ideal) := by
    apply Subtype.ext
    exact conjugacyClassSum_mul_coeff left right (conjugacyClassRepresentative result)
  rw [hcoordinate, map_natCast]

@[expose] def coefficientBlockDefect {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) (label : basis.index) (defect : Subgroup group) : Prop :=
  (∃ conjugacyClass : ConjClasses group, classDefect prime conjugacyClass defect ∧
    centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ conjugacyClass) ≠ 0) ∧
  ∀ (conjugacyClass : ConjClasses group) (other : Subgroup group),
    classDefect prime conjugacyClass other →
    centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ conjugacyClass) ≠ 0 →
    subgroupSubconjugate defect other

theorem coefficientBlockDefect_isPGroup {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {prime : ℕ} {label : basis.index} {defect : Subgroup group}
    (hdefect : coefficientBlockDefect basis ideal prime label defect) : IsPGroup prime defect := by
  obtain ⟨_, hclass, _⟩ := hdefect.1
  exact classDefect_isPGroup hclass

theorem coefficientBlockDefect_conjugate {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {prime : ℕ} {label : basis.index} {left right : Subgroup group}
    (hleft : coefficientBlockDefect basis ideal prime label left)
    (hright : coefficientBlockDefect basis ideal prime label right) : subgroupsConjugate left right := by
  obtain ⟨leftClass, hleftClass, hleftValue⟩ := hleft.1
  obtain ⟨rightClass, hrightClass, hrightValue⟩ := hright.1
  exact subgroupSubconjugate_antisymm (hleft.2 rightClass right hrightClass hrightValue)
    (hright.2 leftClass left hleftClass hleftValue)

theorem coefficientBlockDefect_exists {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (label : basis.index) : ∃ defect : Subgroup group, coefficientBlockDefect basis ideal prime label defect := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  let : Fintype (ConjClasses group) := Fintype.ofFinite _
  let candidate : ℕ → Prop := fun order =>
    ∃ (conjugacyClass : ConjClasses group) (defect : Subgroup group),
      classDefect prime conjugacyClass defect ∧
      centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ conjugacyClass) ≠ 0 ∧
      Nat.card defect = order
  have hexists : ∃ order, candidate order := by
    obtain ⟨defect, hdefect⟩ := classDefect_exists prime (ConjClasses.mk (1 : group))
    refine ⟨Nat.card defect, ConjClasses.mk (1 : group), defect, hdefect, ?_, rfl⟩
    rw [centralConjugacyClassSum_one, map_one]
    exact one_ne_zero
  obtain ⟨selected, defect, hdefect, hvalue, horder⟩ := Nat.find_spec hexists
  refine ⟨defect, ⟨selected, hdefect, hvalue⟩, ?_⟩
  intro otherClass other hother hotherValue
  have hproduct : centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ selected) *
      centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ otherClass) ≠ 0 :=
    mul_ne_zero hvalue hotherValue
  rw [centralCharacterResidueHom_class_product] at hproduct
  obtain ⟨result, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hproduct
  have hcoefficient : ¬prime ∣
      classProductCoefficient selected otherClass (conjugacyClassRepresentative result) := by
    intro hdivides
    apply hterm
    rw [(CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) prime _).mpr hdivides, zero_mul]
  have hresultValue : centralCharacterResidueHom basis ideal label
      (centralConjugacyClassSum _ result) ≠ 0 := by
    intro hzero
    apply hterm
    rw [hzero, mul_zero]
  obtain ⟨resultDefect, hresultDefect⟩ := classDefect_exists prime result
  have hminimal : Nat.card defect ≤ Nat.card resultDefect := by
    rw [horder]
    exact Nat.find_min' hexists ⟨result, resultDefect, hresultDefect, hresultValue, rfl⟩
  obtain ⟨hfirst, hsecond⟩ := classProduct_defect_containment prime selected otherClass result
    (conjugacyClassRepresentative result) (conjugacyClassRepresentative_spec result) hcoefficient
      hresultDefect hdefect hother
  have hconjugate := subgroupsConjugate_of_subconjugate_card_ge hfirst hminimal
  exact subgroupSubconjugate_trans (subgroupsConjugate_subconjugate (subgroupsConjugate_symm hconjugate))
    hsecond

theorem coefficientBlockDefect_iff_of_same_block {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) {left right : basis.index}
    (hblock : sameCoefficientBlock basis (localizedComplexIntegerRing ideal) left right)
    (defect : Subgroup group) :
    coefficientBlockDefect basis ideal prime left defect ↔ coefficientBlockDefect basis ideal prime right defect := by
  have hequal := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal left right).mp hblock
  unfold coefficientBlockDefect
  rw [hequal]

end CFSG.TwoRankLowerBound.Helpers
