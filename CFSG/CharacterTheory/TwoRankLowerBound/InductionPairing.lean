module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormThree

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem subgroup_conditional_sum {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) :
    (∑ element : G, if hmember : element ∈ subgroup then function ⟨element, hmember⟩ else 0) =
      ∑ element : subgroup, function element := by
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  apply Fintype.sum_equiv
    ({ toFun := fun element => ⟨element.val, (Finset.mem_filter.mp element.property).2⟩
       invFun := fun element => ⟨element.val, by simp [element.property]⟩
       left_inv := by intro element; rfl
       right_inv := by intro element; rfl } :
      (Finset.univ.filter (fun element : G => element ∈ subgroup)) ≃ subgroup)
  intro element
  rfl

theorem inducedFunction_conjugate {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) (element conjugator : G) :
    inducedFunction subgroup function (conjugator * element * conjugator⁻¹) =
      inducedFunction subgroup function element := by
  unfold inducedFunction
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft conjugator⁻¹)
  intro argument
  change (if hmember : argument⁻¹ * (conjugator * element * conjugator⁻¹) * argument ∈ subgroup
      then function ⟨argument⁻¹ * (conjugator * element * conjugator⁻¹) * argument, hmember⟩ else 0) =
    if hmember : (conjugator⁻¹ * argument)⁻¹ * element * (conjugator⁻¹ * argument) ∈ subgroup
      then function ⟨(conjugator⁻¹ * argument)⁻¹ * element * (conjugator⁻¹ * argument), hmember⟩ else 0
  have hequal : argument⁻¹ * (conjugator * element * conjugator⁻¹) * argument =
      (conjugator⁻¹ * argument)⁻¹ * element * (conjugator⁻¹ * argument) := by group
  simp only [hequal]

theorem characterPairing_inducedFunction_left {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) (classFunction : G → ℂ)
    (hinvariant : ∀ element conjugator : G,
      classFunction (conjugator * element * conjugator⁻¹) = classFunction element) :
    characterPairing (inducedFunction subgroup function) classFunction =
      characterPairing function (fun element : subgroup => classFunction element) := by
  unfold characterPairing inducedFunction
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hreindex : ∀ conjugator : G,
      (∑ element : G,
        (if hmember : conjugator⁻¹ * element * conjugator ∈ subgroup then
          function ⟨conjugator⁻¹ * element * conjugator, hmember⟩ else 0) * classFunction element⁻¹) =
      ∑ member : subgroup, function member * classFunction (member : G)⁻¹ := by
    intro conjugator
    trans ∑ element : G,
      if hmember : element ∈ subgroup then
        function ⟨element, hmember⟩ * classFunction element⁻¹ else 0
    · apply Fintype.sum_equiv (MulAut.conj conjugator⁻¹).toEquiv
      intro element
      have hequal : classFunction element⁻¹ =
          classFunction (conjugator⁻¹ * element * conjugator)⁻¹ := by
        have hvalue := hinvariant element⁻¹ conjugator⁻¹
        simpa only [inv_inv, mul_inv_rev, mul_assoc] using hvalue.symm
      simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply,
        inv_inv, hequal]
      split_ifs <;> simp
    · exact subgroup_conditional_sum subgroup
        (fun member => function member * classFunction (member : G)⁻¹)
  simp only [mul_assoc] at hreindex
  simp only [hreindex, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  rfl

theorem inducedFunction_eq_on_trivial_intersection_support {G : Type*}
    [Group G] [Fintype G] (subgroup : Subgroup G) (support : Set G)
    (function : subgroup → ℂ)
    (hinvariant : ∀ element conjugator : subgroup,
      function (conjugator * element * conjugator⁻¹) = function element)
    (hsupport : ∀ element : subgroup, (element : G) ∉ support → function element = 0)
    (hintersection : ∀ element ∈ support, ∀ conjugator : G, conjugator ∉ subgroup →
      conjugator⁻¹ * element * conjugator ∉ support)
    (element : subgroup) (hmember : (element : G) ∈ support) :
    inducedFunction subgroup function element = function element := by
  unfold inducedFunction
  have hterms : ∀ conjugator : G,
      (if hconjugate : conjugator⁻¹ * (element : G) * conjugator ∈ subgroup then
        function ⟨conjugator⁻¹ * (element : G) * conjugator, hconjugate⟩ else 0) =
      if conjugator ∈ subgroup then function element else 0 := by
    intro conjugator
    by_cases hconjugator : conjugator ∈ subgroup
    · have hconjugate : conjugator⁻¹ * (element : G) * conjugator ∈ subgroup :=
        subgroup.mul_mem (subgroup.mul_mem (subgroup.inv_mem hconjugator) element.property)
          hconjugator
      rw [dite_eq_left hconjugate, ite_eq_left hconjugator]
      have hvalue := hinvariant element (⟨conjugator, hconjugator⟩ : subgroup)⁻¹
      rw [inv_inv] at hvalue
      exact hvalue
    · rw [ite_eq_right hconjugator]
      split_ifs with hconjugate
      · exact hsupport ⟨_, hconjugate⟩ (hintersection element hmember conjugator hconjugator)
      · rfl
  simp_rw [hterms]
  have hsum : (∑ conjugator : G, if conjugator ∈ subgroup then function element else 0) =
      (Nat.card subgroup : ℂ) * function element := by
    have hconditional := subgroup_conditional_sum subgroup
      (fun _member : subgroup => function element)
    simpa only [dite_eq_ite, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card] using hconditional
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

theorem characterPairing_inducedFunction_norm_of_trivial_intersection {G : Type*}
    [Group G] [Fintype G] (subgroup : Subgroup G) (support : Set G)
    (function : subgroup → ℂ)
    (hinvariant : ∀ element conjugator : subgroup,
      function (conjugator * element * conjugator⁻¹) = function element)
    (hsupport : ∀ element : subgroup, (element : G) ∉ support → function element = 0)
    (hinversion : ∀ element ∈ support, element⁻¹ ∈ support)
    (hintersection : ∀ element ∈ support, ∀ conjugator : G, conjugator ∉ subgroup →
      conjugator⁻¹ * element * conjugator ∉ support) :
    characterPairing (inducedFunction subgroup function) (inducedFunction subgroup function) =
      characterPairing function function := by
  rw [characterPairing_inducedFunction_left subgroup function _
    (inducedFunction_conjugate subgroup function)]
  unfold characterPairing
  congr 1
  apply Finset.sum_congr rfl
  intro element _
  change function element * inducedFunction subgroup function (element⁻¹ : subgroup) =
    function element * function element⁻¹
  by_cases hmember : (element : G) ∈ support
  · rw [inducedFunction_eq_on_trivial_intersection_support subgroup support function
      hinvariant hsupport hintersection element⁻¹ (hinversion element hmember)]
  · rw [hsupport element hmember, zero_mul, zero_mul]

theorem characterPairing_inducedFunction_principal {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) :
    characterPairing (inducedFunction subgroup function) 1 = characterPairing function 1 := by
  exact characterPairing_inducedFunction_left subgroup function 1 (by intros; rfl)

theorem inducedFunction_eq_zero_of_support_avoids_conjugates {G : Type*}
    [Group G] [Fintype G] (subgroup : Subgroup G) (support : Set G)
    (function : subgroup → ℂ)
    (hsupport : ∀ element : subgroup, (element : G) ∉ support → function element = 0)
    (element : G) (havoid : ∀ conjugator : G, conjugator⁻¹ * element * conjugator ∉ support) :
    inducedFunction subgroup function element = 0 := by
  unfold inducedFunction
  rw [Finset.sum_eq_zero, mul_zero]
  intro conjugator _
  split_ifs with hmember
  · exact hsupport ⟨_, hmember⟩ (havoid conjugator)
  · rfl

theorem rank_one_root_local_virtual_character_contradicts_simple {G : Type*}
    [Group G] [Fintype G] [IsSimpleGroup G]
    (hrank : CFSG.Open.twoRank G ≤ 1)
    (involution : G) (horder : orderOf involution = 2)
    (subgroup : Subgroup G) (support : Set G) (function : subgroup → ℂ)
    (hvirtual : function ∈ virtualCharacters subgroup)
    (hinvariant : ∀ element conjugator : subgroup,
      function (conjugator * element * conjugator⁻¹) = function element)
    (hsupport : ∀ element : subgroup, (element : G) ∉ support → function element = 0)
    (hinversion : ∀ element ∈ support, element⁻¹ ∈ support)
    (hintersection : ∀ element ∈ support, ∀ conjugator : G, conjugator ∉ subgroup →
      conjugator⁻¹ * element * conjugator ∉ support)
    (hroots : support ⊆ cyclicRootSet involution)
    (hprincipal : characterPairing function 1 = 1)
    (hnorm : characterPairing function function = 3)
    (hinvolution : ∀ conjugator : G, conjugator⁻¹ * involution * conjugator ∉ support) :
    False := by
  apply virtual_character_norm_three_involution_product_contradicts_simple involution horder
    (inducedFunction subgroup function) (inducedFunction_mem_virtualCharacters subgroup hvirtual)
  · rw [characterPairing_inducedFunction_principal]
    exact hprincipal
  · rw [characterPairing_inducedFunction_norm_of_trivial_intersection subgroup support function
      hinvariant hsupport hinversion hintersection]
    exact hnorm
  · apply inducedFunction_eq_zero_of_support_avoids_conjugates subgroup support function hsupport
    intro conjugator
    simp only [mul_one, inv_mul_cancel]
    exact fun hmember => one_not_mem_cyclicRootSet involution
      (orderOf_eq_prime_iff.mp horder).2 (hroots hmember)
  · exact inducedFunction_eq_zero_of_support_avoids_conjugates subgroup support function hsupport
      involution hinvolution
  · exact induced_involution_root_supported_function_vanishes involution horder
      (centralizer_unique_involution_of_twoRank_le_one hrank involution horder) subgroup function
      (fun element hnot => hsupport element (fun hmember => hnot (hroots hmember)))

end CFSG.TwoRankLowerBound.Helpers
