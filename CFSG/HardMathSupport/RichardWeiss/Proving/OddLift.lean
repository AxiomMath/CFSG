module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

theorem two_pow_mod_three_mem (k : ℕ) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

theorem sq_eq_inv_of_orderOf_eq_three {H : Type*} [Group H] {x : H} (h3 : orderOf x = 3) :
    x ^ 2 = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, show 2 + 1 = orderOf x by rw [h3]]
  exact pow_orderOf_eq_one x

theorem exists_pow_two_pow_odd_orderOf_univ {G : Type*} [Group G] [Finite G] (y : G) :
    ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  have hd : 2 ^ k ∣ orderOf y := hk ▸ dvd_mul_right _ _
  rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) hd]
  have : orderOf y / 2 ^ k = m := by
    rw [hk]
    exact Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (pow_ne_zero k two_ne_zero))
  rw [this]
  exact hm

theorem exists_odd_pow_two_pow_map_eq {G H : Type*} [Group G] [Finite G] [Group H] (θ : G →* H)
    {g : G} (h3 : orderOf (θ g) = 3) :
    ∃ k : ℕ, Odd (orderOf (g ^ 2 ^ k)) ∧ (θ (g ^ 2 ^ k) = θ g ∨ θ (g ^ 2 ^ k) = (θ g)⁻¹) := by
  obtain ⟨k, hk⟩ := exists_pow_two_pow_odd_orderOf_univ g
  refine ⟨k, hk, ?_⟩
  rw [map_pow, ← pow_mod_orderOf, h3]
  rcases two_pow_mod_three_mem k with h | h
  · left
    rw [h, pow_one]
  · right
    rw [h, sq_eq_inv_of_orderOf_eq_three h3]

end CFSG.HardMathSupport.RichardWeiss.Proving

end
