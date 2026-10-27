module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset

theorem sqrt_pow_lt_pow_sub_one {P : ℝ} (hP : 5 ≤ P) {k : ℕ} (hk : 3 ≤ k) :
    Real.sqrt (P ^ (k + 2)) < P ^ k - 1 := by
  have hone : (1 : ℝ) < P ^ k := one_lt_pow₀ (by linarith) (by omega)
  have h1 : P ^ (k + 3) ≤ P ^ (2 * k) := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : P ^ k ≤ P ^ (k + 2) := pow_le_pow_right₀ (by linarith) (by omega)
  have hn0 : (0 : ℝ) < P ^ (k + 2) := by positivity
  have e1 : P ^ (k + 3) = P ^ (k + 2) * P := by ring
  have e2 : P ^ (2 * k) = (P ^ k) ^ 2 := by ring
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith [h1, h2, hn0]

theorem one_lt_of_abs_mul_sub_geomSum_sq_le {p q n m : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (hn : n = p ^ q) (hm : m = ∑ i ∈ range q, p ^ i) {e : ℝ}
    (h : |(n : ℝ) * e - (m : ℝ) ^ 2| ≤ (n : ℝ) * Real.sqrt (n : ℝ)) :
    1 < e := by
  have hP : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  subst hn hm
  push_cast at h ⊢
  set P : ℝ := (p : ℝ) with hPdef
  have hn0 : (0 : ℝ) < P ^ (k + 2) := by positivity
  have hm : P ^ (k + 1) ≤ ∑ i ∈ range (k + 2), P ^ i := by
    refine Finset.single_le_sum (f := fun i => P ^ i) (fun i _ => by positivity) ?_
    simp
  have hm2 : P ^ (k + 2) * P ^ k ≤ (∑ i ∈ range (k + 2), P ^ i) ^ 2 := by
    have hrw : P ^ (k + 2) * P ^ k = (P ^ (k + 1)) ^ 2 := by ring
    rw [hrw]
    exact pow_le_pow_left₀ (by positivity) hm 2
  have hsqrt := sqrt_pow_lt_pow_sub_one hP hk
  rw [abs_le] at h
  have key : P ^ (k + 2) * 1 < P ^ (k + 2) * e := by
    nlinarith [h.1, hm2, mul_lt_mul_of_pos_left hsqrt hn0]
  exact lt_of_mul_lt_mul_left key hn0.le

end

end CFSG.FeitThompson
