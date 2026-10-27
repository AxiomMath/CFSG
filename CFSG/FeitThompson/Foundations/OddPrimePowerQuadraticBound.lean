module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem four_mul_sq_add_one_lt_three_pow {n : ℕ} (hn : 5 ≤ n) : 4 * n ^ 2 + 1 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc 4 * (n + 1) ^ 2 + 1 < 3 * (4 * n ^ 2 + 1) := by nlinarith
      _ < 3 * 3 ^ n := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 3 ^ (n + 1) := by ring

theorem four_mul_sq_add_one_lt_pow_of_odd_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hpq : p ≠ q) : 4 * q ^ 2 + 1 < p ^ q := by
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqodd
  rcases eq_or_lt_of_le hq3 with hq' | hq'
  ·
    subst hq'
    have hp1 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    have hp5 : 5 ≤ p := by omega
    calc 4 * 3 ^ 2 + 1 < 5 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
  ·
    have hq1 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    have hq5 : 5 ≤ q := by omega
    calc 4 * q ^ 2 + 1 < 3 ^ q := four_mul_sq_add_one_lt_three_pow hq5
      _ ≤ p ^ q := Nat.pow_le_pow_left hp3 q

end CFSG.FeitThompson
