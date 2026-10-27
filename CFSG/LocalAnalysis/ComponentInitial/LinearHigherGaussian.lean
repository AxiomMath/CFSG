module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Finset

@[expose] def gaussianCoeff (n k q : ℕ) : ℚ :=
  ∏ i ∈ range k, (((q : ℚ) ^ (n - i) - 1) / ((q : ℚ) ^ (k - i) - 1))

@[expose] def qFactorialProd (m q : ℕ) : ℚ :=
  ∏ j ∈ range m, ((q : ℚ) ^ (j + 1) - 1)

variable {q : ℕ}

theorem qFactorialProd_succ (m q : ℕ) :
    qFactorialProd (m + 1) q = qFactorialProd m q * ((q : ℚ) ^ (m + 1) - 1) :=
  prod_range_succ _ _

theorem pow_sub_one_pos (hq : 2 ≤ q) {m : ℕ} (hm : 1 ≤ m) : 0 < (q : ℚ) ^ m - 1 := by
  have h1 : (1 : ℚ) < q := by exact_mod_cast hq
  have := one_lt_pow₀ h1 (by omega : m ≠ 0)
  linarith

theorem qFactorialProd_pos (hq : 2 ≤ q) (m : ℕ) : 0 < qFactorialProd m q :=
  prod_pos fun j _ => pow_sub_one_pos hq (by omega)

theorem prod_pow_sub_one_eq (k q : ℕ) :
    ∏ i ∈ range k, ((q : ℚ) ^ (k - i) - 1) = qFactorialProd k q := by
  rw [qFactorialProd, ← prod_range_reflect (fun j => (q : ℚ) ^ (j + 1) - 1) k]
  refine prod_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [show k - 1 - i + 1 = k - i by omega]

theorem prod_pow_sub_one_mul (q : ℕ) {n : ℕ} :
    ∀ k ≤ n, (∏ i ∈ range k, ((q : ℚ) ^ (n - i) - 1)) * qFactorialProd (n - k) q =
      qFactorialProd n q := by
  intro k
  induction k with
  | zero => intro _; rw [prod_range_zero, one_mul, Nat.sub_zero]
  | succ k ih =>
    intro hk
    rw [prod_range_succ, ← ih (by omega), show n - k = n - (k + 1) + 1 by omega,
      qFactorialProd_succ, show n - (k + 1) + 1 = n - k by omega]
    ring

theorem gaussianCoeff_eq (hq : 2 ≤ q) {n k : ℕ} (hk : k ≤ n) :
    gaussianCoeff n k q = qFactorialProd n q / (qFactorialProd k q * qFactorialProd (n - k) q) := by
  have h1 := prod_pow_sub_one_mul q k hk
  have h2 := qFactorialProd_pos hq (n - k)
  have h3 := qFactorialProd_pos hq k
  rw [gaussianCoeff, prod_div_distrib, prod_pow_sub_one_eq, ← h1]
  field_simp

theorem gaussianCoeff_symm (hq : 2 ≤ q) {n k : ℕ} (hk : k ≤ n) :
    gaussianCoeff n k q = gaussianCoeff n (n - k) q := by
  rw [gaussianCoeff_eq hq hk, gaussianCoeff_eq hq (Nat.sub_le n k), Nat.sub_sub_self hk,
    mul_comm (qFactorialProd k q)]

theorem gaussianCoeff_succ (hq : 2 ≤ q) {n k : ℕ} (hk : k < n) :
    gaussianCoeff n (k + 1) q =
      gaussianCoeff n k q * (((q : ℚ) ^ (n - k) - 1) / ((q : ℚ) ^ (k + 1) - 1)) := by
  have h1 := qFactorialProd_pos hq (n - (k + 1))
  have h2 := qFactorialProd_pos hq k
  have h3 := pow_sub_one_pos hq (m := k + 1) (by omega)
  have h4 := pow_sub_one_pos hq (m := n - k) (by omega)
  rw [gaussianCoeff_eq hq hk, gaussianCoeff_eq hq hk.le, qFactorialProd_succ,
    show n - k = n - (k + 1) + 1 by omega, qFactorialProd_succ, show n - (k + 1) + 1 = n - k by
      omega]
  field_simp

theorem gaussianCoeff_one (n q : ℕ) :
    gaussianCoeff n 1 q = ((q : ℚ) ^ n - 1) / ((q : ℚ) - 1) := by
  simp [gaussianCoeff]

theorem gaussianCoeff_lt_succ (hq : 2 ≤ q) {n k : ℕ} (hk : k + 1 < n - k) :
    gaussianCoeff n k q < gaussianCoeff n (k + 1) q := by
  have hpos : 0 < gaussianCoeff n k q := by
    rw [gaussianCoeff_eq hq (by omega)]
    have := qFactorialProd_pos hq n
    have := qFactorialProd_pos hq k
    have := qFactorialProd_pos hq (n - k)
    positivity
  have h3 := pow_sub_one_pos hq (m := k + 1) (by omega)
  have hlt : (q : ℚ) ^ (k + 1) - 1 < (q : ℚ) ^ (n - k) - 1 := by
    have h1 : (1 : ℚ) < q := by exact_mod_cast hq
    have := pow_lt_pow_right₀ h1 hk
    linarith
  rw [gaussianCoeff_succ hq (by omega)]
  have hratio : 1 < ((q : ℚ) ^ (n - k) - 1) / ((q : ℚ) ^ (k + 1) - 1) := by
    rw [one_lt_div h3]
    exact hlt
  calc gaussianCoeff n k q = gaussianCoeff n k q * 1 := (mul_one _).symm
    _ < _ := mul_lt_mul_of_pos_left hratio hpos

theorem gaussianCoeff_one_lt (hq : 2 ≤ q) {n : ℕ} :
    ∀ k, 2 ≤ k → 2 * k ≤ n → gaussianCoeff n 1 q < gaussianCoeff n k q := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk hkn
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      exact gaussianCoeff_lt_succ hq (by omega)
    · exact (ih hk2 (by omega)).trans (gaussianCoeff_lt_succ hq (by omega))

theorem gaussian_minimum {q n : ℕ} (hq : 2 ≤ q) (hn : 3 ≤ n) {k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) :
    gaussianCoeff n 1 q = ((q : ℚ) ^ n - 1) / ((q : ℚ) - 1) ∧
      gaussianCoeff n 1 q ≤ gaussianCoeff n k q ∧
      (gaussianCoeff n k q = gaussianCoeff n 1 q ↔ k = 1 ∨ k = n - 1) := by
  have hstrict : k ≠ 1 → k ≠ n - 1 → gaussianCoeff n 1 q < gaussianCoeff n k q := by
    intro h1 h2
    rcases le_or_gt (2 * k) n with hkn' | hkn'
    · exact gaussianCoeff_one_lt hq k (by omega) hkn'
    · rw [gaussianCoeff_symm hq hkn.le]
      exact gaussianCoeff_one_lt hq (n - k) (by omega) (by omega)
  have hend : k = 1 ∨ k = n - 1 → gaussianCoeff n k q = gaussianCoeff n 1 q := by
    rintro (rfl | rfl)
    · rfl
    · rw [gaussianCoeff_symm hq (Nat.sub_le n 1), Nat.sub_sub_self (by omega)]
  refine ⟨gaussianCoeff_one n q, ?_, ⟨fun h => ?_, hend⟩⟩
  · by_cases h : k = 1 ∨ k = n - 1
    · exact (hend h).ge
    · push Not at h
      exact (hstrict h.1 h.2).le
  · by_contra hne
    push Not at hne
    exact (hstrict hne.1 hne.2).ne' h

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
