module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem two_mul_add_one_le_pow_of_three_le {p : ℕ} (hp : 3 ≤ p) (a : ℕ) :
    2 * a + 1 ≤ p ^ a := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith

theorem arith_contra_two {p n β q a : ℕ} (hp : 7 ≤ p) (h1 : p ^ 2 ≤ n)
    (h2 : p ^ 2 * β ≤ 2 * n + p ^ 2) (hq : q = (n - 4) / p) (h4 : q * p ^ a ≤ a + β) :
    False := by
  have hpa := two_mul_add_one_le_pow_of_three_le (by omega : 3 ≤ p) a
  have hp2' : p ^ 2 = p * p := by ring
  rw [hp2'] at h1 h2
  have hn4 : 4 + p + 3 ≤ n := by nlinarith
  have hq1 : p * q ≤ n - 4 := by rw [hq]; exact Nat.mul_div_le _ _
  have hq2 : n - 4 < p * (q + 1) := by
    rw [hq]
    exact Nat.lt_mul_div_succ (n - 4) (show 0 < p by omega)
  have hn4' : n - 4 + 4 = n := by omega
  have hqβ : q ≤ β := by
    by_contra h
    have h5 : β + 1 ≤ q := by omega
    have h6 : q * (2 * a + 1) ≤ q * p ^ a := Nat.mul_le_mul_left q hpa
    nlinarith
  have h7 : n ≤ p * β + p + 3 := by
    have : p * q ≤ p * β := Nat.mul_le_mul_left p hqβ
    have hexp : p * (q + 1) = p * q + p := by ring
    omega
  have h8 : p - 1 ≤ β := by
    by_contra h
    have h9 : β + 2 ≤ p := by omega
    have : p * β + p + 3 < p * p := by nlinarith
    omega
  nlinarith

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
