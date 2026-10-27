module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralClassCoordinates
public import CFSG.CharacterTheory.TwoRankLowerBound.ClassDefectRelations

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem conjugacyClass_mk_conjugation {group : Type*} [Group group]
    (element conjugator : group) :
    ConjClasses.mk (conjugator * element * conjugator⁻¹) = ConjClasses.mk element :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨conjugator⁻¹, by group⟩)

abbrev classProductFiber {group : Type*} [Group group]
    (left right : ConjClasses group) (product : group) :=
  {element : group // ConjClasses.mk element = left ∧ ConjClasses.mk (element⁻¹ * product) = right}

@[expose] noncomputable def classProductCoefficient {group : Type*} [Group group] [Finite group]
    (left right : ConjClasses group) (product : group) : ℕ :=
  Nat.card (classProductFiber left right product)

theorem conjugacyClassSum_mul_coeff {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group]
    (left right : ConjClasses group) (product : group) :
    (conjugacyClassSum (ring := ring) left * conjugacyClassSum right).coeff product =
      (classProductCoefficient left right product : ring) := by
  rw [groupAlgebra_coeff_mul_fintype]
  simp only [conjugacyClassSum_coeff]
  have hproduct : ∀ element : group,
      (if ConjClasses.mk element = left then (1 : ring) else 0) *
        (if ConjClasses.mk (element⁻¹ * product) = right then 1 else 0) =
      if ConjClasses.mk element = left ∧ ConjClasses.mk (element⁻¹ * product) = right then 1 else 0 := by
    intro element
    split_ifs <;> simp_all
  simp only [hproduct, Finset.sum_boole]
  change _ = (Nat.card (classProductFiber left right product) : ring)
  rw [Nat.card_eq_fintype_card]
  congr 1
  exact (Fintype.card_subtype _).symm

theorem classProductCoefficient_conjugation {group : Type*} [Group group] [Fintype group]
    (left right : ConjClasses group) (product conjugator : group) :
    classProductCoefficient left right (conjugator * product * conjugator⁻¹) =
      classProductCoefficient left right product := by
  let value : centralCoefficientSubring (G := group) (⊤ : Subring ℂ) :=
    centralConjugacyClassSum ⊤ left * centralConjugacyClassSum ⊤ right
  have hequal := central_groupAlgebra_coeff_conjugation value.val
    (centralCoefficientSubring_commutes ⊤ value) product conjugator
  change (conjugacyClassSum (ring := ℂ) left * conjugacyClassSum right).coeff
      (conjugator * product * conjugator⁻¹) =
    (conjugacyClassSum left * conjugacyClassSum right).coeff product at hequal
  rw [conjugacyClassSum_mul_coeff, conjugacyClassSum_mul_coeff] at hequal
  exact Nat.cast_injective hequal

theorem classProductCoefficient_eq_of_class {group : Type*} [Group group] [Fintype group]
    (left right : ConjClasses group) {first second : group}
    (hclass : ConjClasses.mk first = ConjClasses.mk second) :
    classProductCoefficient left right first = classProductCoefficient left right second := by
  obtain ⟨conjugator, hequal⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  rw [← hequal, classProductCoefficient_conjugation]

@[expose, instance_reducible] noncomputable def classProductFiberAction {group : Type*} [Group group]
    (primary : Subgroup group) (left right : ConjClasses group) (product : group)
    (hcentralizes : primary ≤ Subgroup.centralizer ({product} : Set group)) :
    MulAction primary (classProductFiber left right product) where
  smul conjugator point := ⟨conjugator.val * point.val * conjugator.val⁻¹, by
    constructor
    · rw [conjugacyClass_mk_conjugation, point.property.1]
    · have hfixed : (MulAut.conj conjugator.val) product = product := by
        have hcommute := Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes conjugator.property)
        change conjugator.val * product * conjugator.val⁻¹ = product
        rw [hcommute]
        group
      have hequal : (conjugator.val * point.val * conjugator.val⁻¹)⁻¹ * product =
          conjugator.val * (point.val⁻¹ * product) * conjugator.val⁻¹ := by
        change ((MulAut.conj conjugator.val) point.val)⁻¹ * product =
          (MulAut.conj conjugator.val) (point.val⁻¹ * product)
        rw [map_mul, map_inv, hfixed]
      rw [hequal, conjugacyClass_mk_conjugation, point.property.2]⟩
  one_smul point := Subtype.ext (by change 1 * point.val * 1⁻¹ = point.val; group)
  mul_smul first second point := Subtype.ext (by
    change (first.val * second.val) * point.val * (first.val * second.val)⁻¹ =
      first.val * (second.val * point.val * second.val⁻¹) * first.val⁻¹
    group)

theorem p_subgroup_classProduct_fixed_pair {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group) (hprimary : IsPGroup prime primary)
    (left right : ConjClasses group) (product : group)
    (hcentralizes : primary ≤ Subgroup.centralizer ({product} : Set group))
    (hcoefficient : ¬prime ∣ classProductCoefficient left right product) :
    ∃ first second : group, ConjClasses.mk first = left ∧ ConjClasses.mk second = right ∧
      first * second = product ∧
      primary ≤ Subgroup.centralizer ({first} : Set group) ∧
      primary ≤ Subgroup.centralizer ({second} : Set group) := by
  let : MulAction primary (classProductFiber left right product) :=
    classProductFiberAction primary left right product hcentralizes
  obtain ⟨point, hfixed⟩ := hprimary.nonempty_fixed_point_of_prime_not_dvd_card
    (classProductFiber left right product) hcoefficient
  have hfirst : primary ≤ Subgroup.centralizer ({point.val} : Set group) := by
    intro member hmember
    have hequal := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hfixed (⟨member, hmember⟩ : primary))
    change member * point.val * member⁻¹ = point.val at hequal
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    calc
      member * point.val = (member * point.val * member⁻¹) * member := by group
      _ = point.val * member := by rw [hequal]
  refine ⟨point.val, point.val⁻¹ * product, point.property.1, point.property.2,
    by group, hfirst, ?_⟩
  intro member hmember
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hleft : Commute member point.val := Subgroup.mem_centralizer_singleton_iff.mp (hfirst hmember)
  have hright : Commute member product := Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes hmember)
  exact hleft.inv_right.mul_right hright

theorem classProduct_defect_containment {group : Type*} [Group group] [Fintype group]
    (prime : ℕ) [Fact prime.Prime] (left right result : ConjClasses group) (product : group)
    (hproduct : ConjClasses.mk product = result)
    (hcoefficient : ¬prime ∣ classProductCoefficient left right product)
    {resultDefect leftDefect rightDefect : Subgroup group}
    (hresult : classDefect prime result resultDefect)
    (hleft : classDefect prime left leftDefect) (hright : classDefect prime right rightDefect) :
    subgroupSubconjugate resultDefect leftDefect ∧ subgroupSubconjugate resultDefect rightDefect := by
  obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hresult
  have hcoefficient' : ¬prime ∣ classProductCoefficient left right representative := by
    rwa [classProductCoefficient_eq_of_class left right (hrepresentative.trans hproduct.symm)]
  obtain ⟨first, second, hfirst, hsecond, _, hcentralizesFirst, hcentralizesSecond⟩ :=
    p_subgroup_classProduct_fixed_pair prime _ (sylow.isPGroup'.map _) left right representative
      (sylow_image_le _ sylow) hcoefficient'
  exact ⟨p_subgroup_subconjugate_classDefect prime _ (sylow.isPGroup'.map _) first
      hcentralizesFirst hfirst hleft,
    p_subgroup_subconjugate_classDefect prime _ (sylow.isPGroup'.map _) second
      hcentralizesSecond hsecond hright⟩

end CFSG.TwoRankLowerBound.Helpers
