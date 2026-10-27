module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Assembly.OrderReductions.InvolutionGraph

public section

namespace CFSG.OrderReductions.InvolutionFusion

open CFSG.OrderReductions.InvolutionGraph

theorem involution_mul_self {group : Type*} [Group group] (involution : Involution group) :
    involution.val * involution.val = 1 := by
  have square_one := pow_orderOf_eq_one involution.val
  simpa only [involution.property, pow_two] using square_one

theorem product_conjugate_inv {group : Type*} [Group group]
    (first second : Involution group) :
    (MulAut.conj first.val) (first.val * second.val) = (first.val * second.val)⁻¹ := by
  rw [MulAut.conj_apply, ← mul_assoc, involution_mul_self, one_mul, mul_inv_rev,
    inv_eq_self_of_orderOf_eq_two second.property]

theorem product_power_conjugate_inv {group : Type*} [Group group]
    (first second : Involution group) (exponent : ℕ) :
    (MulAut.conj first.val) ((first.val * second.val) ^ exponent) =
      ((first.val * second.val) ^ exponent)⁻¹ := by
  rw [map_pow, product_conjugate_inv, inv_pow]

theorem reachable_of_even_product_order {group : Type*} [Group group] [Finite group]
    (first second : Involution group) (even_order : Even (orderOf (first.val * second.val))) :
    (commutingGraph group).Reachable first second := by
  let product := first.val * second.val
  let central_element := product ^ (orderOf product / 2)
  have central_order : orderOf central_element = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos product)) even_order.two_dvd
  let central : Involution group := ⟨central_element, central_order⟩
  have first_fixes : (MulAut.conj first.val) central_element = central_element := by
    rw [product_power_conjugate_inv first second]
    exact inv_eq_self_of_orderOf_eq_two central_order
  have first_commutes : Commute first.val central_element := by
    change first.val * central_element = central_element * first.val
    have equal_conjugate := congrArg (fun element : group => element * first.val) first_fixes
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using equal_conjugate
  have product_commutes : Commute product central_element := (Commute.refl product).pow_right _
  have second_commutes : Commute second.val central_element := by
    have equal_second : second.val = first.val * product := by
      dsimp [product]
      rw [← mul_assoc, involution_mul_self, one_mul]
    rw [equal_second]
    exact first_commutes.mul_left product_commutes
  exact (reachable_of_commute first central first_commutes).trans
    (reachable_of_commute second central second_commutes).symm

theorem odd_product_conjugator_smul {group : Type*} [Group group]
    (first second : Involution group) (half : ℕ)
    (order_eq : orderOf (first.val * second.val) = 2 * half + 1) :
    ((first.val * second.val) ^ half) • first = second := by
  let product := first.val * second.val
  have conjugate_power := product_power_conjugate_inv first second half
  have moves_power : first.val * (product ^ half)⁻¹ = product ^ half * first.val := by
    have conjugate_inverse := congrArg Inv.inv conjugate_power
    have multiplied := congrArg (fun element : group => element * first.val) conjugate_inverse
    simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      using multiplied
  have product_full : product ^ (half + half + 1) = 1 := by
    have order_power := pow_orderOf_eq_one product
    rw [show orderOf product = half + half + 1 from by dsimp [product]; omega] at order_power
    exact order_power
  have product_double : product ^ (half + half) = product⁻¹ := by
    have multiplied := congrArg (fun element : group => element * product⁻¹) product_full
    simpa only [pow_succ, mul_assoc, mul_inv_cancel, mul_one, one_mul] using multiplied
  change (product ^ half) • first = second
  apply Subtype.ext
  rw [involution_smul_val, mul_assoc, moves_power, ← mul_assoc, ← pow_add, product_double]
  dsimp [product]
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one,
    inv_eq_self_of_orderOf_eq_two second.property]

theorem conjugate_of_odd_product_order {group : Type*} [Group group]
    (first second : Involution group) (odd_order : Odd (orderOf (first.val * second.val))) :
    ∃ conjugator : group, conjugator • first = second := by
  obtain ⟨half, order_eq⟩ := odd_order
  exact ⟨(first.val * second.val) ^ half, odd_product_conjugator_smul first second half order_eq⟩

theorem odd_product_order_of_not_reachable {group : Type*} [Group group] [Finite group]
    (first second : Involution group)
    (not_reachable : ¬ (commutingGraph group).Reachable first second) :
    Odd (orderOf (first.val * second.val)) := by
  apply Nat.not_even_iff_odd.mp
  intro even_order
  exact not_reachable (reachable_of_even_product_order first second even_order)

theorem all_involutions_conjugate_of_disconnected {group : Type*} [Group group] [Finite group]
    (disconnected : ¬ (commutingGraph group).Preconnected)
    (first second : Involution group) : ∃ conjugator : group, conjugator • first = second := by
  classical
  by_cases reachable : (commutingGraph group).Reachable first second
  · have outside : ∃ other : Involution group,
        ¬ (commutingGraph group).Reachable first other := by
      by_contra no_outside
      push Not at no_outside
      exact disconnected (fun vertex other => (no_outside vertex).symm.trans (no_outside other))
    obtain ⟨other, not_first⟩ := outside
    have not_second : ¬ (commutingGraph group).Reachable second other := by
      intro second_reachable
      exact not_first (reachable.trans second_reachable)
    obtain ⟨first_conjugator, first_conjugates⟩ := conjugate_of_odd_product_order first other
      (odd_product_order_of_not_reachable first other not_first)
    obtain ⟨second_conjugator, second_conjugates⟩ := conjugate_of_odd_product_order second other
      (odd_product_order_of_not_reachable second other not_second)
    refine ⟨second_conjugator⁻¹ * first_conjugator, ?_⟩
    rw [mul_smul, first_conjugates, ← second_conjugates, inv_smul_smul]
  · exact conjugate_of_odd_product_order first second
      (odd_product_order_of_not_reachable first second reachable)

theorem involution_swapping_components {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) :
    ∃ involution : Involution group,
      involution.val • first = second ∧ involution.val • second = first := by
  induction first, second using SimpleGraph.ConnectedComponent.ind₂ with
  | h first second =>
      have not_reachable : ¬ (commutingGraph group).Reachable first second := by
        intro reachable
        exact distinct (SimpleGraph.ConnectedComponent.sound reachable)
      obtain ⟨half, odd_order⟩ := odd_product_order_of_not_reachable first second not_reachable
      let product := first.val * second.val
      let reflection := product ^ half * first.val
      have conjugated_power := product_power_conjugate_inv first second half
      have moves_power : first.val * product ^ half = (product ^ half)⁻¹ * first.val := by
        have multiplied := congrArg (fun element : group => element * first.val) conjugated_power
        simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using multiplied
      have reflection_square : reflection ^ 2 = 1 := by
        dsimp [reflection]
        rw [pow_two, mul_assoc, ← mul_assoc first.val, moves_power, mul_assoc,
          ← mul_assoc, mul_inv_cancel, one_mul, involution_mul_self]
      have moves_first : reflection • first = second := by
        change (product ^ half * first.val) • first = second
        rw [mul_smul]
        have first_fixes : first.val • first = first := by
          apply Subtype.ext
          rw [involution_smul_val, involution_mul_self, one_mul,
            inv_eq_self_of_orderOf_eq_two first.property]
        rw [first_fixes]
        exact odd_product_conjugator_smul first second half odd_order
      have reflection_ne_one : reflection ≠ 1 := by
        intro equal_one
        rw [equal_one, one_smul] at moves_first
        exact distinct (congrArg (commutingGraph group).connectedComponentMk moves_first)
      have reflection_order : orderOf reflection = 2 := by
        rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
          (orderOf_dvd_of_pow_eq_one reflection_square) with order_one | order_two
        · exact False.elim (reflection_ne_one (orderOf_eq_one_iff.mp order_one))
        · exact order_two
      let involution : Involution group := ⟨reflection, reflection_order⟩
      refine ⟨involution, ?_, ?_⟩
      · rw [componentMk_smul, moves_first]
      · change reflection • (commutingGraph group).connectedComponentMk second = _
        rw [← moves_first, ← componentMk_smul reflection first, ← mul_smul,
          show reflection * reflection = 1 from
          by simpa only [pow_two] using reflection_square, one_smul]

theorem involution_card_mul_centralizer_card {group : Type*} [Group group] [Finite group]
    (transitive : MulAction.IsPretransitive group (Involution group))
    (involution : Involution group) :
    Nat.card (Involution group) * Nat.card (Subgroup.centralizer ({involution.val} : Set group)) =
      Nat.card group := by
  classical
  let _ : Fintype group := Fintype.ofFinite group
  let _ : Fintype (Involution group) := Fintype.ofFinite _
  have := transitive
  have orbit_card : Nat.card (MulAction.orbit group involution) =
      Nat.card (Involution group) := by
    rw [MulAction.orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ _)
  let _ : Fintype (MulAction.stabilizer group involution) := Fintype.ofFinite _
  have card_product := MulAction.card_orbit_mul_card_stabilizer_eq_card_group group involution
  simp only [← Nat.card_eq_fintype_card] at card_product
  rw [orbit_card, involution_stabilizer_eq_centralizer] at card_product
  exact card_product

theorem involution_conjugator_of_odd_product_order {group : Type*} [Group group]
    (first second : Involution group) (distinct : first ≠ second)
    (odd_order : Odd (orderOf (first.val * second.val))) :
    ∃ conjugator : Involution group, conjugator.val • first = second := by
  obtain ⟨half, order_eq⟩ := odd_order
  let product := first.val * second.val
  let reflection := product ^ half * first.val
  have conjugate_power := product_power_conjugate_inv first second half
  have moves_power : first.val * product ^ half = (product ^ half)⁻¹ * first.val := by
    have multiplied := congrArg (fun element : group => element * first.val) conjugate_power
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using multiplied
  have reflection_square : reflection ^ 2 = 1 := by
    dsimp [reflection]
    rw [pow_two, mul_assoc, ← mul_assoc first.val, moves_power, mul_assoc,
      ← mul_assoc, mul_inv_cancel, one_mul, involution_mul_self]
  have moves_first : reflection • first = second := by
    change (product ^ half * first.val) • first = second
    rw [mul_smul]
    have first_fixes : first.val • first = first := by
      apply Subtype.ext
      rw [involution_smul_val, involution_mul_self, one_mul,
        inv_eq_self_of_orderOf_eq_two first.property]
    rw [first_fixes]
    exact odd_product_conjugator_smul first second half order_eq
  have reflection_ne_one : reflection ≠ 1 := by
    intro equal_one
    rw [equal_one, one_smul] at moves_first
    exact distinct moves_first
  have reflection_order : orderOf reflection = 2 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
      (orderOf_dvd_of_pow_eq_one reflection_square) with order_one | order_two
    · exact False.elim (reflection_ne_one (orderOf_eq_one_iff.mp order_one))
    · exact order_two
  exact ⟨⟨reflection, reflection_order⟩, moves_first⟩

@[expose] def commutingProduct {group : Type*} [Group group]
    (first second : Involution group) (distinct : first ≠ second)
    (commuting : Commute first.val second.val) : Involution group :=
  ⟨first.val * second.val, by
    have square_one : (first.val * second.val) ^ 2 = 1 := by
      rw [commuting.mul_pow]
      have first_square := pow_orderOf_eq_one first.val
      have second_square := pow_orderOf_eq_one second.val
      rw [first.property] at first_square
      rw [second.property] at second_square
      rw [first_square, second_square, one_mul]
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
      (orderOf_dvd_of_pow_eq_one square_one) with order_one | order_two
    · have product_one := orderOf_eq_one_iff.mp order_one
      have multiplied := congrArg (fun element : group => element * second.val) product_one
      have equal_values : first.val = second.val := by
        simpa only [mul_assoc, involution_mul_self, mul_one, one_mul] using multiplied
      exact False.elim (distinct (Subtype.ext equal_values))
    · exact order_two⟩

theorem involution_card_ge_three_of_commuting {group : Type*} [Group group] [Finite group]
    (first second : Involution group) (distinct : first ≠ second)
    (commuting : Commute first.val second.val) : 3 ≤ Nat.card (Involution group) := by
  classical
  let _ : Fintype (Involution group) := Fintype.ofFinite _
  let product := commutingProduct first second distinct commuting
  have first_ne_product : first ≠ product := by
    intro equal_vertices
    have equal_values := congrArg Subtype.val equal_vertices
    change first.val = first.val * second.val at equal_values
    have second_one : second.val = 1 := by
      have multiplied := congrArg (fun element : group => first.val⁻¹ * element) equal_values
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using multiplied.symm
    have order_one := second.property
    rw [second_one, orderOf_one] at order_one
    omega
  have second_ne_product : second ≠ product := by
    intro equal_vertices
    have equal_values := congrArg Subtype.val equal_vertices
    change second.val = first.val * second.val at equal_values
    have first_one : first.val = 1 := by
      have multiplied := congrArg (fun element : group => element * second.val⁻¹) equal_values
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using multiplied.symm
    have order_one := first.property
    rw [first_one, orderOf_one] at order_one
    omega
  have triple_card : ({first, second, product} : Finset (Involution group)).card = 3 := by
    simp [distinct, first_ne_product, second_ne_product]
  have card_bound := Finset.card_le_univ ({first, second, product} : Finset (Involution group))
  simpa only [triple_card, Finset.card_univ, Nat.card_eq_fintype_card] using card_bound

end CFSG.OrderReductions.InvolutionFusion
