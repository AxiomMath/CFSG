module

public import CFSG.Assembly.OrderReductions.TIClassFunctionInduction
public import CFSG.Assembly.OrderReductions.CharacterCoefficients

public section

namespace CFSG.OrderReductions.TIInductionIsometry

open CFSG.OrderReductions.TIClassFunctionInduction
open CFSG.OrderReductions.CharacterCoefficients
open scoped Classical

@[expose] def ClassFunction {group field : Type*} [Group group] (function : group → field) : Prop :=
  ∀ element conjugator, function (conjugator * element * conjugator⁻¹) = function element

theorem zeroExtension_weighted_sum {field group : Type*} [Field field] [Group group] [Fintype group]
    (subgroup : Subgroup group) (function : subgroup → field) (weight : group → field) :
    (∑ element : group, zeroExtension subgroup function element * weight element) =
      ∑ element : subgroup, function element * weight element.val := by
  classical
  let inside : Finset group := Finset.univ.filter (fun element => element ∈ subgroup)
  have restrict : (∑ element : group, zeroExtension subgroup function element * weight element) =
      ∑ element ∈ inside, zeroExtension subgroup function element * weight element := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro element _ outside
    have not_mem : element ∉ subgroup := by simpa only [inside, Finset.mem_filter, Finset.mem_univ, true_and] using outside
    rw [zeroExtension, dite_eq_right not_mem, zero_mul]
  rw [restrict, Finset.sum_subtype (p := fun element : group => element ∈ subgroup)
    inside (fun element => by simp [inside])]
  apply Finset.sum_congr rfl
  intro element _
  rw [zeroExtension, dite_eq_left element.property]

theorem conjugate_weighted_sum {field group : Type*} [Field field] [Group group] [Fintype group]
    (function weight : group → field) (class_weight : ClassFunction weight) (conjugator : group) :
    (∑ element : group, function (conjugator * element * conjugator⁻¹) * weight element⁻¹) =
      ∑ element : group, function element * weight element⁻¹ := by
  apply Fintype.sum_equiv (MulAut.conj conjugator).toEquiv
  intro element
  congr 1
  change weight element⁻¹ = weight (conjugator * element * conjugator⁻¹)⁻¹
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using (class_weight element⁻¹ conjugator).symm

theorem frobenius_reciprocity {field group : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] (subgroup : Subgroup group) (function : subgroup → field)
    (weight : group → field) (class_weight : ClassFunction weight) :
    scalarProduct (inducedFunction subgroup function) weight =
      scalarProduct function (fun element : subgroup => weight element.val) := by
  classical
  have group_card_ne_zero : (Nat.card group : field) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)
  have numerator : (∑ element : group,
      (∑ conjugator : group, zeroExtension subgroup function (conjugator * element * conjugator⁻¹)) *
        weight element⁻¹) =
      (Nat.card group : field) * ∑ element : subgroup, function element * weight element.val⁻¹ := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [conjugate_weighted_sum (zeroExtension subgroup function) weight class_weight,
      zeroExtension_weighted_sum subgroup function (fun element => weight element⁻¹)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  simp only [scalarProduct, inducedFunction, mul_assoc, ← Finset.mul_sum]
  simp only [mul_assoc] at numerator
  rw [numerator]
  field_simp
  simp only [Subgroup.coe_inv]

theorem inducedFunction_class {field group : Type*} [Field field] [Group group] [Fintype group]
    (subgroup : Subgroup group) (function : subgroup → field) : ClassFunction (inducedFunction subgroup function) := by
  intro element conjugator
  unfold inducedFunction
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight conjugator)
  intro current
  congr 1
  change current * (conjugator * element * conjugator⁻¹) * current⁻¹ =
    (current * conjugator) * element * (current * conjugator)⁻¹
  group

theorem zeroExtension_conjugate_of_mem {field group : Type*} [Field field] [Group group]
    (subgroup : Subgroup group) (function : subgroup → field) (class_function : ClassFunction function)
    (conjugator : subgroup) (element : group) :
    zeroExtension subgroup function (conjugator.val * element * conjugator.val⁻¹) =
      zeroExtension subgroup function element := by
  classical
  by_cases membership : element ∈ subgroup
  · have conjugate_mem := subgroup.mul_mem (subgroup.mul_mem conjugator.property membership)
      (subgroup.inv_mem conjugator.property)
    rw [zeroExtension, zeroExtension, dite_eq_left membership, dite_eq_left conjugate_mem]
    exact class_function ⟨element, membership⟩ conjugator
  · have conjugate_not_mem : conjugator.val * element * conjugator.val⁻¹ ∉ subgroup := by
      intro conjugate_mem
      apply membership
      have restored := subgroup.mul_mem (subgroup.mul_mem (subgroup.inv_mem conjugator.property) conjugate_mem)
        conjugator.property
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using restored
    rw [zeroExtension, zeroExtension, dite_eq_right membership, dite_eq_right conjugate_not_mem]

theorem inducedFunction_on_support {field group : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] (subgroup : Subgroup group) (support : Set group)
    (ti : CFSG.OrderReductions.TIInvolutionProducts.TI support subgroup)
    (function : subgroup → field) (class_function : ClassFunction function)
    (supported : ∀ element : subgroup, element.val ∉ support → function element = 0)
    (element : subgroup) (element_mem : element.val ∈ support) :
    inducedFunction subgroup function element.val = function element := by
  classical
  have subgroup_card_ne_zero : (Nat.card subgroup : field) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)
  have all_terms : ∀ conjugator : group,
      zeroExtension subgroup function (conjugator * element.val * conjugator⁻¹) =
        zeroExtension subgroup (fun _ => function element) conjugator := by
    intro conjugator
    by_cases membership : conjugator ∈ subgroup
    · rw [zeroExtension_conjugate_of_mem subgroup function class_function ⟨conjugator, membership⟩,
        zeroExtension, dite_eq_left element.property, zeroExtension, dite_eq_left membership]
    · have conjugate_outside : conjugator * element.val * conjugator⁻¹ ∉ support := by
        intro conjugate_mem
        exact membership (CFSG.OrderReductions.TIInvolutionProducts.mem_normalizer_of_overlap support subgroup ti
          conjugator element.val element_mem conjugate_mem)
      simp only [zeroExtension, dite_eq_right membership]
      by_cases conjugate_mem : conjugator * element.val * conjugator⁻¹ ∈ subgroup
      · rw [dite_eq_left conjugate_mem]
        exact supported _ conjugate_outside
      · rw [dite_eq_right conjugate_mem]
  unfold inducedFunction
  simp_rw [all_terms]
  have sum_eq := zeroExtension_weighted_sum subgroup (fun _ => function element) (fun _ => (1 : field))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card] at sum_eq
  rw [sum_eq, ← mul_assoc, inv_mul_cancel₀ subgroup_card_ne_zero, one_mul]

theorem ti_induction_isometry {field group : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] (subgroup : Subgroup group) (support : Set group)
    (ti : CFSG.OrderReductions.TIInvolutionProducts.TI support subgroup)
    (inverse_stable : ∀ element ∈ support, element⁻¹ ∈ support)
    (first second : subgroup → field) (class_second : ClassFunction second)
    (supported_first : ∀ element : subgroup, element.val ∉ support → first element = 0)
    (supported_second : ∀ element : subgroup, element.val ∉ support → second element = 0) :
    scalarProduct (inducedFunction subgroup first) (inducedFunction subgroup second) =
      scalarProduct first second := by
  rw [frobenius_reciprocity subgroup first (inducedFunction subgroup second)
    (inducedFunction_class subgroup second)]
  unfold scalarProduct
  congr 1
  apply Finset.sum_congr rfl
  intro element _
  change first element * inducedFunction subgroup second element.val⁻¹ = first element * second element⁻¹
  by_cases membership : element.val ∈ support
  · have value_eq := inducedFunction_on_support subgroup support ti second class_second supported_second
      element⁻¹ (inverse_stable element.val membership)
    simpa only [Subgroup.coe_inv] using congrArg (fun value => first element * value) value_eq
  · rw [supported_first element membership, zero_mul, zero_mul]

end CFSG.OrderReductions.TIInductionIsometry
