module

public import CFSG.Assembly.OrderReductions.CharacterClassProducts
public import CFSG.Assembly.OrderReductions.TIInvolutionProducts

public section

namespace CFSG.OrderReductions.TIClassFunctionInduction

open CFSG.OrderReductions.InvolutionGraph

@[expose] noncomputable def zeroExtension {field group : Type*} [Field field] [Group group]
    (subgroup : Subgroup group) (function : subgroup → field) (element : group) : field := by
  classical
  exact if membership : element ∈ subgroup then function ⟨element, membership⟩ else 0

@[expose] noncomputable def inducedFunction {field group : Type*} [Field field] [Group group] [Fintype group]
    (subgroup : Subgroup group) (function : subgroup → field) (element : group) : field :=
  (Nat.card subgroup : field)⁻¹ *
    ∑ conjugator : group, zeroExtension subgroup function (conjugator * element * conjugator⁻¹)

theorem conjugated_pair_sum {field group : Type*} [Field field] [Group group]
    (first_set second_set : Finset group) (function : group → field)
    (first_stable : ∀ conjugator element, element ∈ first_set →
      conjugator * element * conjugator⁻¹ ∈ first_set)
    (second_stable : ∀ conjugator element, element ∈ second_set →
      conjugator * element * conjugator⁻¹ ∈ second_set) (conjugator : group) :
    (∑ first ∈ first_set, ∑ second ∈ second_set,
      function (conjugator * (first * second) * conjugator⁻¹)) =
      ∑ first ∈ first_set, ∑ second ∈ second_set, function (first * second) := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_product']
  apply Finset.sum_bij'
    (fun pair _ => (conjugator * pair.1 * conjugator⁻¹, conjugator * pair.2 * conjugator⁻¹))
    (fun pair _ => (conjugator⁻¹ * pair.1 * conjugator, conjugator⁻¹ * pair.2 * conjugator))
  · intro pair membership
    obtain ⟨first_mem, second_mem⟩ := Finset.mem_product.mp membership
    exact Finset.mem_product.mpr
      ⟨first_stable conjugator pair.1 first_mem, second_stable conjugator pair.2 second_mem⟩
  · intro pair membership
    obtain ⟨first_mem, second_mem⟩ := Finset.mem_product.mp membership
    apply Finset.mem_product.mpr
    constructor
    · simpa only [inv_inv] using first_stable conjugator⁻¹ pair.1 first_mem
    · simpa only [inv_inv] using second_stable conjugator⁻¹ pair.2 second_mem
  · intro pair membership
    apply Prod.ext <;> dsimp <;> group
  · intro pair membership
    apply Prod.ext <;> dsimp <;> group
  · intro pair membership
    dsimp
    congr 1
    group

theorem induced_pair_sum {field group : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] (subgroup : Subgroup group) (function : subgroup → field)
    (first_set second_set : Finset group)
    (first_stable : ∀ conjugator element, element ∈ first_set →
      conjugator * element * conjugator⁻¹ ∈ first_set)
    (second_stable : ∀ conjugator element, element ∈ second_set →
      conjugator * element * conjugator⁻¹ ∈ second_set) :
    (∑ first ∈ first_set, ∑ second ∈ second_set, inducedFunction subgroup function (first * second)) =
      (subgroup.index : field) *
        ∑ first ∈ first_set, ∑ second ∈ second_set, zeroExtension subgroup function (first * second) := by
  classical
  have cardinality_eq : (Nat.card group : field) = (Nat.card subgroup : field) * subgroup.index := by
    exact_mod_cast subgroup.card_mul_index.symm
  have subgroup_card_ne_zero : (Nat.card subgroup : field) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)
  simp only [inducedFunction, ← Finset.mul_sum]
  rw [Finset.sum_comm_cycle]
  simp_rw [conjugated_pair_sum first_set second_set (zeroExtension subgroup function)
    first_stable second_stable]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, cardinality_eq]
  field_simp

theorem extension_involution_product_zero {field group : Type*} [Field field] [Group group]
    (subgroup : Subgroup group) (support : Set group)
    (ti : CFSG.OrderReductions.TIInvolutionProducts.TI support subgroup)
    (inverse_stable : ∀ element ∈ support, element⁻¹ ∈ support)
    (function : subgroup → field)
    (supported : ∀ element : subgroup, element.val ∉ support → function element = 0)
    (local_zero : ∀ first second : Involution subgroup, function (first.val * second.val) = 0)
    (first second : Involution group) : zeroExtension subgroup function (first.val * second.val) = 0 := by
  classical
  by_cases membership : first.val * second.val ∈ subgroup
  · rw [zeroExtension, dite_eq_left membership]
    by_cases support_mem : first.val * second.val ∈ support
    · obtain ⟨first_mem, second_mem⟩ :=
        CFSG.OrderReductions.TIInvolutionProducts.product_in_support_factors_mem_normalizer
          support subgroup ti inverse_stable first second support_mem
      let internal_first : Involution subgroup :=
        ⟨⟨first.val, first_mem⟩, by rw [← Subgroup.orderOf_coe]; exact first.property⟩
      let internal_second : Involution subgroup :=
        ⟨⟨second.val, second_mem⟩, by rw [← Subgroup.orderOf_coe]; exact second.property⟩
      exact local_zero internal_first internal_second
    · exact supported _ support_mem
  · rw [zeroExtension, dite_eq_right membership]

theorem induced_involution_class_square_zero {field group : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] (subgroup : Subgroup group) (support : Set group)
    (ti : CFSG.OrderReductions.TIInvolutionProducts.TI support subgroup)
    (inverse_stable : ∀ element ∈ support, element⁻¹ ∈ support)
    (function : subgroup → field)
    (supported : ∀ element : subgroup, element.val ∉ support → function element = 0)
    (local_zero : ∀ first second : Involution subgroup, function (first.val * second.val) = 0)
    (involution : Involution group) :
    (∑ first ∈ CFSG.OrderReductions.CharacterClassProducts.conjugacyFinset involution.val,
      ∑ second ∈ CFSG.OrderReductions.CharacterClassProducts.conjugacyFinset involution.val,
        inducedFunction subgroup function (first * second)) = 0 := by
  rw [induced_pair_sum subgroup function _ _
    (CFSG.OrderReductions.CharacterClassProducts.conjugacyFinset_stable involution.val)
    (CFSG.OrderReductions.CharacterClassProducts.conjugacyFinset_stable involution.val)]
  suffices pair_sum : (∑ first ∈ CFSG.OrderReductions.CharacterClassProducts.conjugacyFinset involution.val,
      ∑ second ∈ CFSG.OrderReductions.CharacterClassProducts.conjugacyFinset involution.val,
        zeroExtension subgroup function (first * second)) = 0 by rw [pair_sum, mul_zero]
  apply Finset.sum_eq_zero
  intro first first_mem
  apply Finset.sum_eq_zero
  intro second second_mem
  have first_order : orderOf first = 2 := by
    obtain ⟨conjugator, equal⟩ := isConj_iff.mp
      ((CFSG.OrderReductions.CharacterClassProducts.mem_conjugacyFinset involution.val first).mp first_mem)
    rw [← equal]
    exact (MulAut.conj conjugator).orderOf_eq involution.val |>.trans involution.property
  have second_order : orderOf second = 2 := by
    obtain ⟨conjugator, equal⟩ := isConj_iff.mp
      ((CFSG.OrderReductions.CharacterClassProducts.mem_conjugacyFinset involution.val second).mp second_mem)
    rw [← equal]
    exact (MulAut.conj conjugator).orderOf_eq involution.val |>.trans involution.property
  exact extension_involution_product_zero subgroup support ti inverse_stable function supported local_zero
    ⟨first, first_order⟩ ⟨second, second_order⟩

theorem induced_one_zero_of_punctured_support {field group : Type*} [Field field] [Group group]
    [Fintype group] (subgroup : Subgroup group) (support : Set group) (one_not_mem : (1 : group) ∉ support)
    (function : subgroup → field)
    (supported : ∀ element : subgroup, element.val ∉ support → function element = 0) :
    inducedFunction subgroup function 1 = 0 := by
  classical
  unfold inducedFunction
  suffices all_zero : (∑ conjugator : group,
      zeroExtension subgroup function (conjugator * 1 * conjugator⁻¹)) = 0 by rw [all_zero, mul_zero]
  apply Finset.sum_eq_zero
  intro conjugator _
  simp only [mul_one, mul_inv_cancel, zeroExtension, dite_eq_left (subgroup.one_mem)]
  exact supported _ one_not_mem

theorem induced_involution_zero_of_support {field group : Type*} [Field field] [Group group]
    [Fintype group] (subgroup : Subgroup group) (support : Set group)
    (no_involutions : ∀ element ∈ support, orderOf element ≠ 2)
    (function : subgroup → field)
    (supported : ∀ element : subgroup, element.val ∉ support → function element = 0)
    (involution : Involution group) : inducedFunction subgroup function involution.val = 0 := by
  classical
  unfold inducedFunction
  suffices all_zero : (∑ conjugator : group,
      zeroExtension subgroup function (conjugator * involution.val * conjugator⁻¹)) = 0 by
    rw [all_zero, mul_zero]
  apply Finset.sum_eq_zero
  intro conjugator _
  by_cases membership : conjugator * involution.val * conjugator⁻¹ ∈ subgroup
  · rw [zeroExtension, dite_eq_left membership]
    apply supported
    intro support_mem
    apply no_involutions _ support_mem
    exact (MulAut.conj conjugator).orderOf_eq involution.val |>.trans involution.property
  · rw [zeroExtension, dite_eq_right membership]

theorem proper_normal_of_supported_norm_three_decomposition
    {field group first_vector second_vector : Type*}
    [Field field] [CharZero field] [IsAlgClosed field] [Group group] [Fintype group]
    [AddCommGroup first_vector] [Module field first_vector] [FiniteDimensional field first_vector]
    [AddCommGroup second_vector] [Module field second_vector] [FiniteDimensional field second_vector]
    (subgroup : Subgroup group) (support : Set group)
    (ti : CFSG.OrderReductions.TIInvolutionProducts.TI support subgroup)
    (inverse_stable : ∀ element ∈ support, element⁻¹ ∈ support)
    (no_involutions : ∀ element ∈ support, orderOf element ≠ 2)
    (function : subgroup → field)
    (supported : ∀ element : subgroup, element.val ∉ support → function element = 0)
    (local_zero : ∀ first second : Involution subgroup, function (first.val * second.val) = 0)
    (first : Representation field group first_vector) [first.IsIrreducible]
    (second : Representation field group second_vector) [second.IsIrreducible]
    (nontrivial_first : first ≠ 1) (first_coefficient second_coefficient : field)
    (first_coefficient_ne_zero : first_coefficient ≠ 0)
    (second_coefficient_ne_zero : second_coefficient ≠ 0)
    (first_degree_ne_zero : first.character 1 ≠ 0) (second_degree_ne_zero : second.character 1 ≠ 0)
    (decomposition : ∀ element : group, inducedFunction subgroup function element =
      1 + first_coefficient * first.character element - second_coefficient * second.character element)
    (involution : Involution group) :
    ∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊤ ∧ involution.val ∈ normal := by
  apply CFSG.OrderReductions.CharacterClassProducts.proper_normal_of_norm_three_class_square first second
    nontrivial_first involution first_coefficient second_coefficient first_coefficient_ne_zero
    second_coefficient_ne_zero first_degree_ne_zero second_degree_ne_zero
  · rw [← decomposition]
    exact induced_one_zero_of_punctured_support subgroup support ti.2.1 function supported
  · rw [← decomposition]
    exact induced_involution_zero_of_support subgroup support no_involutions function supported involution
  · simp_rw [← decomposition]
    exact induced_involution_class_square_zero subgroup support ti inverse_stable function supported
      local_zero involution

end CFSG.OrderReductions.TIClassFunctionInduction
