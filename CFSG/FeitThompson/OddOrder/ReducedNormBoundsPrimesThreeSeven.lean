module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem eq_three_and_eq_seven_of_pow_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) (hmod : p ≡ 1 [MOD q])
    (hlt : p ^ q < p ^ 2 * q ^ 2) : q = 3 ∧ p = 7 := by
  have hp1 : 1 < p := hp.one_lt
  have hpodd' : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hqodd' : q % 2 = 1 := Nat.odd_iff.mp hqodd
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hq4 : q < 4 := by
    have h : p ^ q < p ^ 4 := by
      calc p ^ q < p ^ 2 * q ^ 2 := hlt
        _ ≤ p ^ 2 * p ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqp.le 2)
        _ = p ^ 4 := by ring
    exact (Nat.pow_lt_pow_iff_right hp1).mp h
  have hq' : q = 3 := by omega
  subst hq'
  refine ⟨rfl, ?_⟩
  have hp9 : p < 9 := by
    have h : p ^ 2 * p < p ^ 2 * 9 := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ < p ^ 2 * 3 ^ 2 := hlt
        _ = p ^ 2 * 9 := by ring
    exact Nat.lt_of_mul_lt_mul_left h
  have hmod' : p % 3 = 1 % 3 := hmod
  omega

end CFSG.FeitThompson
