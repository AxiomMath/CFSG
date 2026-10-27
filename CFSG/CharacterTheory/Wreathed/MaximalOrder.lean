module

public import CFSG.CharacterTheory.Wreathed.Coordinates

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem element_base_eq_one_iff (m : ℕ) (a b : ZMod m) :
    element m a b 0 = 1 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hzero := congrArg (fun g : Wreath m =>
      Multiplicative.toAdd (g.left (Multiplicative.ofAdd 0))) h
    have hone := congrArg (fun g : Wreath m =>
      Multiplicative.toAdd (g.left (Multiplicative.ofAdd 1))) h
    simpa [element] using And.intro hzero hone
  · rintro ⟨rfl, rfl⟩
    exact element_zero m

theorem half_modulus_smul_eq_zero_iff (k : ℕ) (c : ZMod (2 ^ (k + 1))) :
    (2 ^ k) • c = 0 ↔ Even c.val := by
  let : NeZero (2 ^ (k + 1)) := ⟨pow_ne_zero _ (by decide)⟩
  have heq : (2 ^ k) • c = ((2 ^ k * c.val : ℕ) : ZMod (2 ^ (k + 1))) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  rw [heq, ZMod.natCast_eq_zero_iff]
  have hdiv (r : ℕ) : 2 ^ (k + 1) ∣ 2 ^ k * r ↔ 2 ∣ r := by
    rw [pow_succ, Nat.mul_dvd_mul_iff_left (pow_pos (by decide) k)]
  rw [hdiv c.val, even_iff_two_dvd]

theorem element_swap_pow_modulus (k : ℕ) (a b : ZMod (2 ^ (k + 1))) :
    element (2 ^ (k + 1)) a b 1 ^ (2 ^ (k + 1)) =
      element (2 ^ (k + 1)) ((2 ^ k) • (a + b)) ((2 ^ k) • (a + b)) 0 := by
  conv_lhs => arg 2; rw [pow_succ, Nat.mul_comm (2 ^ k) 2]
  rw [pow_mul, element_swap_sq, element_base_pow]

theorem element_swap_maximal_order_iff (k : ℕ) (a b : ZMod (2 ^ (k + 1))) :
    orderOf (element (2 ^ (k + 1)) a b 1) = 2 * 2 ^ (k + 1) ↔
      Odd (a + b).val := by
  have hpow : element (2 ^ (k + 1)) a b 1 ^ (2 ^ (k + 1)) = 1 ↔
      Even (a + b).val := by
    rw [element_swap_pow_modulus, element_base_eq_one_iff,
      half_modulus_smul_eq_zero_iff, and_self]
  constructor
  · intro horder
    apply Nat.not_even_iff_odd.mp
    intro heven
    have hle := orderOf_le_of_pow_eq_one (pow_pos (by decide) (k + 1)) (hpow.mpr heven)
    rw [horder] at hle
    have hpos := pow_pos (by decide : 0 < (2 : ℕ)) (k + 1)
    omega
  · intro hodd
    have hnot : element (2 ^ (k + 1)) a b 1 ^ 2 ^ (k + 1) ≠ 1 := by
      intro hone
      exact Nat.not_even_iff_odd.mpr hodd (hpow.mp hone)
    have hfin : element (2 ^ (k + 1)) a b 1 ^ 2 ^ ((k + 1) + 1) = 1 := by
      simpa only [pow_succ (2 : ℕ) (k + 1), Nat.mul_comm] using
        element_pow_twice_modulus (2 ^ (k + 1)) (element (2 ^ (k + 1)) a b 1)
    simpa only [pow_succ, Nat.mul_comm] using
      (orderOf_eq_prime_pow (p := 2) hnot hfin)

theorem element_base_order_lt_twice_modulus (m : ℕ) (hm : 0 < m) (a b : ZMod m) :
    orderOf (element m a b 0) < 2 * m := by
  have hle := orderOf_le_of_pow_eq_one hm (element_base_pow_modulus m a b)
  omega

theorem element_maximal_order_iff (k : ℕ) (a b : ZMod (2 ^ (k + 1))) (e : ZMod 2) :
    orderOf (element (2 ^ (k + 1)) a b e) = 2 * 2 ^ (k + 1) ↔
      e = 1 ∧ Odd (a + b).val := by
  rcases swap_exponent_cases e with rfl | rfl
  · have hlt := element_base_order_lt_twice_modulus (2 ^ (k + 1))
      (pow_pos (by decide) _) a b
    simp only [zero_ne_one, false_and, iff_false]
    omega
  · simpa only [true_and] using element_swap_maximal_order_iff k a b

end CFSG.Wreathed
