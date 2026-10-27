module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.GroupTheory

theorem pow_eq_self_of_odd_of_mul_self_eq_one {M : Type*} [Monoid M] {x : M}
    (hx : x * x = 1) {n : ℕ} (hn : Odd n) : x ^ n = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

theorem zpow_eq_one_or_self_of_mul_self_eq_one {G : Type*} [Group G] {x : G}
    (hx : x * x = 1) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have h2 : x ^ (2 : ℕ) = 1 := by simpa only [pow_two] using hx
  have hmod : x ^ k = x ^ (k % 2) := zpow_eq_zpow_emod' k h2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hmod, h]; simp
  · right; rw [hmod, h]; simp

end CFSG.GroupTheory
