module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassDefects

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def classProductCount {G : Type*} [Group G] (left right : ConjClasses G)
    (element : G) : ℕ :=
  Nat.card {factor : G // ConjClasses.mk factor = left ∧
    ConjClasses.mk (factor⁻¹ * element) = right}

set_option maxHeartbeats 2000000 in
theorem classProductCount_convolution {G : Type*} [Group G] [Finite G]
    (left right : ConjClasses G) (element : G) :
    coefficientConvolution (classCoefficients left) (classCoefficients right) element =
      (classProductCount left right element : ℂ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [coefficientConvolution_apply]
  have hconditional : ∀ factor : G,
      classCoefficients left factor * classCoefficients right (factor⁻¹ * element) =
      if ConjClasses.mk factor = left ∧ ConjClasses.mk (factor⁻¹ * element) = right
        then (1 : ℂ) else 0 := by
    intro factor
    unfold classCoefficients
    split_ifs <;> simp_all
  trans ∑ factor : G, if ConjClasses.mk factor = left ∧
    ConjClasses.mk (factor⁻¹ * element) = right then (1 : ℂ) else 0
  · apply Finset.sum_congr rfl
    intro factor _
    exact hconditional factor
  rw [Finset.sum_boole]
  simp only [classProductCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem pGroup_exists_fixed_of_not_dvd_card {actingGroup : Type*} [Group actingGroup]
    (prime : ℕ) (hprime : prime.Prime) (hpGroup : IsPGroup prime actingGroup)
    (points : Type*) [MulAction actingGroup points] [Finite points]
    (hcard : ¬ prime ∣ Nat.card points) :
    ∃ point : points, point ∈ MulAction.fixedPoints actingGroup points := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  have hcongruent := hpGroup.card_modEq_card_fixedPoints points
  have hfixedCard : ¬ prime ∣ Nat.card (MulAction.fixedPoints actingGroup points) :=
    fun hdivides => hcard ((hcongruent.dvd_iff (dvd_refl prime)).mpr hdivides)
  have hpositive : 0 < Nat.card (MulAction.fixedPoints actingGroup points) :=
    Nat.pos_of_ne_zero (fun hzero => hfixedCard (hzero ▸ dvd_zero prime))
  obtain ⟨point⟩ := (Nat.card_pos_iff.mp hpositive).1
  exact ⟨point.val, point.property⟩

theorem classProductCount_defect_containment {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (left right : ConjClasses G) (element : G)
    {subgroup : Subgroup G} (hpGroup : IsPGroup prime subgroup)
    (hcentralizes : subgroup ≤ Subgroup.centralizer {element})
    (hcount : ¬ prime ∣ classProductCount left right element)
    {leftDefect rightDefect : Subgroup G}
    (hleftDefect : classDefect prime left leftDefect)
    (hrightDefect : classDefect prime right rightDefect) :
    subgroupSubconjugate subgroup leftDefect ∧
      subgroupSubconjugate subgroup rightDefect := by
  let points := {factor : G // ConjClasses.mk factor = left ∧
    ConjClasses.mk (factor⁻¹ * element) = right}
  have hclassConj : ∀ factor conjugator : G,
      ConjClasses.mk (conjugator * factor * conjugator⁻¹) = ConjClasses.mk factor := by
    intro factor conjugator
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact (isConj_iff.mpr ⟨conjugator, rfl⟩).symm
  have helementFixed : ∀ member : subgroup,
      member.val * element * member.val⁻¹ = element := by
    intro member
    rw [← Subgroup.mem_centralizer_iff.mp (hcentralizes member.property)
      element (Set.mem_singleton element), mul_inv_cancel_right]
  have hsecondFactor : ∀ (member : subgroup) (factor : G),
      (member.val * factor * member.val⁻¹)⁻¹ * element =
        member.val * (factor⁻¹ * element) * member.val⁻¹ := by
    intro member factor
    conv_lhs => rhs; rw [← helementFixed member]
    group
  let : MulAction subgroup points := {
    smul member point := ⟨member.val * point.val * member.val⁻¹, by
      constructor
      · exact (hclassConj _ _).trans point.property.1
      · rw [hsecondFactor, hclassConj]
        exact point.property.2⟩
    one_smul point := Subtype.ext (by
      change (1 : G) * point.val * (1 : G)⁻¹ = point.val
      group)
    mul_smul first second point := Subtype.ext (by
      change (first.val * second.val) * point.val * (first.val * second.val)⁻¹ =
        first.val * (second.val * point.val * second.val⁻¹) * first.val⁻¹
      group)
  }
  obtain ⟨point, hpoint⟩ :=
    pGroup_exists_fixed_of_not_dvd_card prime hprime hpGroup points hcount
  have hfirstCentralizes : subgroup ≤ Subgroup.centralizer {point.val} := by
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    have hfixed := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hpoint ⟨member, hmember⟩)
    change member * point.val * member⁻¹ = point.val at hfixed
    exact ((mul_inv_eq_iff_eq_mul).mp hfixed).symm
  have hsecondCentralizes : subgroup ≤ Subgroup.centralizer {point.val⁻¹ * element} := by
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    have hfixed := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hpoint ⟨member, hmember⟩)
    change member * point.val * member⁻¹ = point.val at hfixed
    have hsecondFixed : member * (point.val⁻¹ * element) * member⁻¹ =
        point.val⁻¹ * element := by
      rw [← hsecondFactor ⟨member, hmember⟩ point.val, hfixed]
    exact ((mul_inv_eq_iff_eq_mul).mp hsecondFixed).symm
  exact ⟨pGroup_centralizes_subconjugate_classDefect prime hprime point.property.1
    hpGroup hfirstCentralizes hleftDefect,
    pGroup_centralizes_subconjugate_classDefect prime hprime point.property.2
    hpGroup hsecondCentralizes hrightDefect⟩

set_option maxHeartbeats 2000000 in
theorem classProductCount_eq_of_class_eq {G : Type*} [Group G] [Finite G]
    (left right : ConjClasses G) {first second : G}
    (hclass : ConjClasses.mk first = ConjClasses.mk second) :
    classProductCount left right first = classProductCount left right second := by
  obtain ⟨conjugator, hconjugator⟩ :=
    isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  have hcentral : ∀ element conjugator : G,
      coefficientConvolution (classCoefficients left) (classCoefficients right)
        (conjugator * element * conjugator⁻¹) =
      coefficientConvolution (classCoefficients left) (classCoefficients right) element := by
    classical
    let : Fintype G := Fintype.ofFinite G
    intro element conjugator
    rw [coefficientConvolution_apply, coefficientConvolution_apply]
    apply Fintype.sum_equiv (MulAut.conj conjugator⁻¹).toEquiv
    intro factor
    have hclassConj : ∀ member conjugating : G,
        ConjClasses.mk (conjugating * member * conjugating⁻¹) = ConjClasses.mk member := by
      intro member conjugating
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr
        (isConj_iff.mpr ⟨conjugating, rfl⟩).symm
    change classCoefficients left factor *
      classCoefficients right (factor⁻¹ * (conjugator * element * conjugator⁻¹)) =
      classCoefficients left (conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹) *
        classCoefficients right ((conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹)⁻¹ * element)
    have hfactor : factor⁻¹ * (conjugator * element * conjugator⁻¹) =
        conjugator * ((conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹)⁻¹ * element) *
          conjugator⁻¹ := by group
    simp only [classCoefficients, hclassConj, hfactor]
    split_ifs <;> rfl
  apply Nat.cast_injective (R := ℂ)
  rw [← classProductCount_convolution, ← classProductCount_convolution, ← hconjugator, hcentral]

theorem classProduct_defect_containment {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (left right : ConjClasses G) (element : G)
    (hcount : ¬ prime ∣ classProductCount left right element)
    {productDefect leftDefect rightDefect : Subgroup G}
    (hproductDefect : classDefect prime (ConjClasses.mk element) productDefect)
    (hleftDefect : classDefect prime left leftDefect)
    (hrightDefect : classDefect prime right rightDefect) :
    subgroupSubconjugate productDefect leftDefect ∧
      subgroupSubconjugate productDefect rightDefect := by
  obtain ⟨representative, hrepresentative, hcentralizes⟩ :=
    classDefect_centralizes prime hproductDefect
  apply classProductCount_defect_containment prime hprime left right representative
    (classDefect_isPGroup prime hproductDefect) hcentralizes
    (by rwa [classProductCount_eq_of_class_eq left right hrepresentative]) hleftDefect hrightDefect

end CFSG.BrauerThirdMainTheorem.Helpers
