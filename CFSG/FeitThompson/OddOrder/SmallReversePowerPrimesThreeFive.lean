module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
import CFSG.FeitThompson.OddOrder.CrossPrimePowerComparison

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem sq_le_three_pow_sub_three {n : ℕ} (hn : 7 ≤ n) : n ^ 2 ≤ 3 ^ (n - 3) := by
  obtain ⟨m, hm, rfl⟩ : ∃ m, 4 ≤ m ∧ n = m + 3 := ⟨n - 3, by omega, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      calc (m + 1 + 3) ^ 2 ≤ 3 * (m + 3) ^ 2 := by nlinarith
        _ ≤ 3 * 3 ^ m := Nat.mul_le_mul_left _ (ih (by omega))
        _ = 3 ^ (m + 1) := by ring

theorem eq_three_and_eq_five_of_pow_sub_three_lt_sq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) (hlt : q ^ (p - 3) < p ^ 2) :
    q = 3 ∧ p = 5 := by
  have hpodd' : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqodd
  have hqeq : q = 3 := by
    by_contra h
    have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three (by omega) h
    have key := pow_succ_lt_pow_succ_of_odd_prime_lt hp hq hpodd hqodd hqp
    have e1 : q ^ (p + 1) = q ^ (p - 3) * q ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have e2 : p ^ 2 * p ^ 4 ≤ p ^ (q + 1) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have e3 : q ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hqp.le 4
    have hq4 : 0 < q ^ 4 := Nat.pow_pos (by omega)
    have e4 : q ^ (p - 3) * q ^ 4 < p ^ 2 * p ^ 4 :=
      calc q ^ (p - 3) * q ^ 4 < p ^ 2 * q ^ 4 :=
            Nat.mul_lt_mul_of_lt_of_le hlt le_rfl hq4
        _ ≤ p ^ 2 * p ^ 4 := Nat.mul_le_mul_left _ e3
    omega
  subst hqeq
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  have hp7 : p < 7 := by
    by_contra h
    exact absurd hlt (not_lt.mpr (sq_le_three_pow_sub_three (by omega)))
  exact ⟨rfl, by omega⟩

end CFSG.FeitThompson
