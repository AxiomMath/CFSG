module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
import CFSG.FeitThompson.OddOrder.CrossPrimePowerComparison
public import Mathlib.Basic.Real.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

theorem mul_geomSum_sub_one_lt_of_odd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hlt : q < p) :
    (p : ℝ) * ((∑ i ∈ range q, (p : ℝ) ^ i) - 1) <
      (q : ℝ) * ((∑ j ∈ range p, (q : ℝ) ^ j) - 1) := by
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqodd
  have hP : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.odd_iff.mp hpodd
  have hQ : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hQP : (q : ℝ) < (p : ℝ) := by exact_mod_cast hlt
  set P := (p : ℝ) with hPdef
  set Q := (q : ℝ) with hQdef
  set A := ∑ i ∈ range q, P ^ i with hA
  set B := ∑ j ∈ range p, Q ^ j with hB
  have hAeq : A * (P - 1) = P ^ q - 1 := geom_sum_mul P q
  have hBeq : B * (Q - 1) = Q ^ p - 1 := geom_sum_mul Q p
  have hkey : P ^ (q + 1) < Q ^ (p + 1) := by
    have h := pow_succ_lt_pow_succ_of_odd_prime_lt hp hq hpodd hqodd hlt
    rw [hPdef, hQdef]; exact_mod_cast h
  have hX : 0 < P ^ (q + 1) - P ^ 2 := by
    have : P ^ 2 < P ^ (q + 1) := pow_lt_pow_right₀ (by linarith) (by omega)
    linarith
  have hQ2P2 : Q ^ 2 < P ^ 2 := by nlinarith
  have hnum : (P ^ (q + 1) - P ^ 2) * (Q - 1) < (Q ^ (p + 1) - Q ^ 2) * (P - 1) := by
    nlinarith
  have h1 : P * (A - 1) * (P - 1) = P ^ (q + 1) - P ^ 2 := by
    have e : P * (A - 1) * (P - 1) = P * (A * (P - 1)) - P * (P - 1) := by ring
    rw [e, hAeq]; ring
  have h2 : Q * (B - 1) * (Q - 1) = Q ^ (p + 1) - Q ^ 2 := by
    have e : Q * (B - 1) * (Q - 1) = Q * (B * (Q - 1)) - Q * (Q - 1) := by ring
    rw [e, hBeq]; ring
  have hd : 0 < (P - 1) * (Q - 1) := by nlinarith
  refine lt_of_mul_lt_mul_right ?_ hd.le
  calc P * (A - 1) * ((P - 1) * (Q - 1)) = P * (A - 1) * (P - 1) * (Q - 1) := by ring
    _ = (P ^ (q + 1) - P ^ 2) * (Q - 1) := by rw [h1]
    _ < (Q ^ (p + 1) - Q ^ 2) * (P - 1) := hnum
    _ = Q * (B - 1) * (Q - 1) * (P - 1) := by rw [h2]
    _ = Q * (B - 1) * ((P - 1) * (Q - 1)) := by ring

theorem sub_one_div_lt_sub_one_div_of_odd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hlt : q < p) {u v : ℝ} (_hu1 : 1 ≤ u)
    (hu : u ≤ ∑ i ∈ range q, (p : ℝ) ^ i) (hv : v = ∑ j ∈ range p, (q : ℝ) ^ j) :
    (u - 1) / q < (v - 1) / p := by
  have hP : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.odd_iff.mp hpodd
  have hQ : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.odd_iff.mp hqodd
  have hmain := mul_geomSum_sub_one_lt_of_odd_prime_lt hp hq hpodd hqodd hlt
  have hPu : (p : ℝ) * (u - 1) ≤ (p : ℝ) * ((∑ i ∈ range q, (p : ℝ) ^ i) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [div_lt_div_iff₀ (by linarith) (by linarith), hv]
  linarith

theorem sub_one_div_lt_sub_one_div_of_odd_prime_lt' {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hlt : q < p) {u v : ℝ} (hu1 : 1 ≤ u)
    (hu : u ≤ ((p : ℝ) ^ q - 1) / ((p : ℝ) - 1)) (hv : v = ((q : ℝ) ^ p - 1) / ((q : ℝ) - 1)) :
    (u - 1) / q < (v - 1) / p := by
  have hP : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.odd_iff.mp hpodd
  have hQ : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.odd_iff.mp hqodd
  have hA : ((p : ℝ) ^ q - 1) / ((p : ℝ) - 1) = ∑ i ∈ range q, (p : ℝ) ^ i := by
    rw [← geom_sum_mul (p : ℝ) q, mul_div_assoc, div_self (by linarith), mul_one]
  have hB : ((q : ℝ) ^ p - 1) / ((q : ℝ) - 1) = ∑ j ∈ range p, (q : ℝ) ^ j := by
    rw [← geom_sum_mul (q : ℝ) p, mul_div_assoc, div_self (by linarith), mul_one]
  rw [hA] at hu
  rw [hB] at hv
  exact sub_one_div_lt_sub_one_div_of_odd_prime_lt hp hq hpodd hqodd hlt hu1 hu hv

end CFSG.FeitThompson
