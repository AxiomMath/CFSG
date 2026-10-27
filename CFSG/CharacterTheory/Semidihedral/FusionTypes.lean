module

public import CFSG.CharacterTheory.Semidihedral.Conjugacy
public import CFSG.CharacterTheory.Semidihedral.ElementStructure

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem conjugate_orderOf_eq {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) : orderOf x = orderOf y := by
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  constructor
  · intro hx
    have hc := h.pow k
    rw [hx, isConj_one_right] at hc
    exact hc
  · intro hy
    have hc := h.symm.pow k
    rw [hy, isConj_one_right] at hc
    exact hc

theorem modulus_ge_eight (n : ℕ) (hn : 4 ≤ n) : 8 ≤ modulus n := by
  have he : n - 1 = (n - 4) + 3 := by omega
  have hp : 0 < 2 ^ (n - 4) := pow_pos (by decide) _
  rw [modulus, he, pow_add]
  norm_num
  omega

theorem even_rotation_order_le_half (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (hi : i.val % 2 = 0) :
    orderOf (element n hn i 0) ≤ half n := by
  apply orderOf_le_of_pow_eq_one (show 0 < half n from pow_pos (by decide) _)
  rw [element_rotation_pow, nsmul_eq_mul,
    (half_mul_eq_zero_iff n hn i).mpr hi, element_zero_zero]

theorem odd_rotation_order (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (hi : i.val % 2 = 1) :
    orderOf (element n hn i 0) = modulus n := by
  have hcop : (modulus n).Coprime i.val := by
    apply Nat.Coprime.pow_left
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro h
    have hz := Nat.mod_eq_zero_of_dvd h
    omega
  rw [element_eq, ZMod.val_zero, pow_zero, mul_one]
  have hc : (orderOf (r n)).Coprime i.val := by
    rw [orderOf_r n hn]
    exact hcop
  rw [hc.orderOf_pow, orderOf_r n hn]

theorem rotation_full_order_iff (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) :
    orderOf (element n (by omega) i 0) = modulus n ↔ i.val % 2 = 1 := by
  constructor
  · intro ho
    by_contra h
    have heven : i.val % 2 = 0 := by omega
    have hb := even_rotation_order_le_half n (by omega) i heven
    have hp : 0 < half n := pow_pos (by decide) _
    have hm := modulus_eq_two_mul_half (by omega : 2 ≤ n)
    omega
  · exact odd_rotation_order n (by omega) i

theorem rotation_order_parity (n : ℕ) (hn : 4 ≤ n)
    (i j : ZMod (modulus n))
    (ho : orderOf (element n (by omega) i 0) =
      orderOf (element n (by omega) j 0)) : i.val % 2 = j.val % 2 := by
  have hi := rotation_full_order_iff n hn i
  have hj := rotation_full_order_iff n hn j
  rw [ho] at hi
  omega

theorem outside_order_parity (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n))
    (ho : orderOf (element n hn i 1) = orderOf (element n hn j 1)) :
    i.val % 2 = j.val % 2 := by
  have hi := outside_involution_iff n hn i
  have hj := outside_involution_iff n hn j
  rw [ho] at hi
  omega

theorem exterior_order_cases (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) :
    orderOf (element n hn i 1) = 2 ∨ orderOf (element n hn i 1) = 4 := by
  by_cases h : i.val % 2 = 0
  · exact Or.inl ((outside_involution_iff n hn i).mpr h)
  · exact Or.inr ((outside_order_four_iff n hn i).mpr (by omega))

theorem rotation_exterior_even (n : ℕ) (hn : 4 ≤ n)
    (i j : ZMod (modulus n))
    (ho : orderOf (element n (by omega) i 0) =
      orderOf (element n (by omega) j 1)) : i.val % 2 = 0 := by
  by_contra h
  have hodd : i.val % 2 = 1 := by omega
  have hfull := odd_rotation_order n (by omega) i hodd
  have hb := modulus_ge_eight n hn
  have hc := exterior_order_cases n (by omega) j
  omega

theorem even_exterior_conjugate (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) (hi : i.val % 2 = 0) :
    IsConj (s n) (element n (by omega) i 1) := by
  rw [s_eq_element n (by omega)]
  apply even_difference_conjugate n hn 0 i ((i.val / 2 : ℕ) : ZMod (modulus n))
  have he : i.val = 2 * (i.val / 2) := by omega
  have hc := congrArg (fun t : ℕ => (t : ZMod (modulus n))) he
  push_cast at hc
  rw [ZMod.natCast_zmod_val] at hc
  simpa only [sub_zero] using hc

theorem odd_exterior_conjugate (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) (hi : i.val % 2 = 1) :
    IsConj (r n * s n) (element n (by omega) i 1) := by
  rw [rotation_generator_eq_element n (by omega), s_eq_element n (by omega),
    element_rotation_mul, add_zero]
  apply even_difference_conjugate n hn 1 i ((i.val / 2 : ℕ) : ZMod (modulus n))
  have he : i.val = 2 * (i.val / 2) + 1 := by omega
  have hc := congrArg (fun t : ℕ => (t : ZMod (modulus n))) he
  push_cast at hc
  rw [ZMod.natCast_zmod_val] at hc
  linear_combination hc

theorem quarter_even (n : ℕ) (hn : 4 ≤ n) : Even (2 ^ (n - 3)) := by
  have he : n - 3 = (n - 4) + 1 := by omega
  refine ⟨2 ^ (n - 4), ?_⟩
  rw [he, pow_succ]
  omega

theorem quarter_inverse_conjugate (n : ℕ) (hn : 4 ≤ n) :
    IsConj (r n ^ (2 ^ (n - 3)))
      (r n ^ (-((2 ^ (n - 3) : ℕ) : ℤ))) := by
  have hm : modulus n = 4 * 2 ^ (n - 3) := by
    rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_quarter (by omega)]
    ring
  have hp : 0 < 2 ^ (n - 3) := pow_pos (by decide) _
  have he : (((2 ^ (n - 3) : ℕ) : ZMod (modulus n))).val % 2 = 0 := by
    rw [ZMod.val_natCast_of_lt (by omega)]
    exact Nat.even_iff.mp (quarter_even n hn)
  have hhalf := (half_mul_eq_zero_iff n (by omega) _).mpr he
  have ht : twist n * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) =
      -((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
    rw [twist, sub_mul, one_mul, hhalf, zero_sub]
  rw [r_pow_eq_element n (by omega), negative_quarter_eq_element n hn,
    rotation_conjugacy_iff]
  exact Or.inr (by rw [ht])

theorem rotation_four_conjugate_quarter (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n))
    (hi : orderOf (element n (by omega) i 0) = 4) :
    IsConj (element n (by omega) i 0) (r n ^ (2 ^ (n - 3))) := by
  rcases (rotation_order_four_iff n hn i).mp hi with rfl | rfl
  · rw [← r_pow_eq_element]
  · rw [← negative_quarter_eq_element n hn]
    exact (quarter_inverse_conjugate n hn).symm

theorem same_parity_difference_mem (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) (e : ZMod 2) (h : i.val % 2 = j.val % 2) :
    (element n hn i e)⁻¹ * element n hn j e ∈ Subgroup.zpowers (r n ^ 2) := by
  have he : rotationReduction n hn i = rotationReduction n hn j := by
    apply ZMod.val_injective
    simpa only [rotationReduction_val] using h
  rw [← abelianizationProjection_ker n hn]
  change abelianizationProjection n hn ((element n hn i e)⁻¹ * element n hn j e) = 1
  rw [map_mul, map_inv, abelianizationProjection_element,
    abelianizationProjection_element, he]
  exact inv_mul_cancel _

end CFSG.Semidihedral
