module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGaussian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Finset LinearFlag

@[expose] def isoGaussian (r k q : ℕ) : ℚ :=
  ∏ i ∈ range k, (((q : ℚ) ^ (2 * (r - i)) - 1) / ((q : ℚ) ^ (k - i) - 1))

variable {q : ℕ}

theorem isoGaussian_eq (r k q : ℕ) :
    isoGaussian r k q = (∏ i ∈ range k, ((q : ℚ) ^ (2 * (r - i)) - 1)) / qFactorialProd k q := by
  rw [isoGaussian, prod_div_distrib, prod_pow_sub_one_eq]

theorem isoGaussian_succ (r k q : ℕ) :
    isoGaussian r (k + 1) q =
      isoGaussian r k q * (((q : ℚ) ^ (2 * (r - k)) - 1) / ((q : ℚ) ^ (k + 1) - 1)) := by
  rw [isoGaussian_eq, isoGaussian_eq, prod_range_succ, qFactorialProd_succ, mul_div_mul_comm]

theorem isoGaussian_pos (hq : 2 ≤ q) {r k : ℕ} (hk : k ≤ r) : 0 < isoGaussian r k q :=
  prod_pos fun i hi => by
    rw [mem_range] at hi
    exact div_pos (pow_sub_one_pos hq (by omega)) (pow_sub_one_pos hq (by omega))

theorem isoGaussian_one (r q : ℕ) :
    isoGaussian r 1 q = ((q : ℚ) ^ (2 * r) - 1) / ((q : ℚ) - 1) := by
  simp [isoGaussian]

theorem isoGaussian_self (hq : 2 ≤ q) (r : ℕ) :
    isoGaussian r r q = ∏ j ∈ range r, ((q : ℚ) ^ (j + 1) + 1) := by
  rw [isoGaussian, ← prod_range_reflect (fun j => (q : ℚ) ^ (j + 1) + 1) r]
  refine prod_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  have hne := (pow_sub_one_pos hq (m := r - i) (by omega)).ne'
  rw [show r - 1 - i + 1 = r - i by omega, mul_comm, pow_mul, div_eq_iff hne]
  ring

theorem isoGaussian_le_succ (hq : 2 ≤ q) {r k : ℕ} (hk : k + 1 ≤ 2 * (r - k)) :
    isoGaussian r k q ≤ isoGaussian r (k + 1) q := by
  have hpos := isoGaussian_pos hq (r := r) (k := k) (by omega)
  have hd := pow_sub_one_pos hq (m := k + 1) (by omega)
  have hle : (q : ℚ) ^ (k + 1) - 1 ≤ (q : ℚ) ^ (2 * (r - k)) - 1 := by
    have h1 : (1 : ℚ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have := pow_le_pow_right₀ h1 hk
    linarith
  rw [isoGaussian_succ]
  calc isoGaussian r k q = isoGaussian r k q * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left ((one_le_div hd).2 hle) hpos.le

theorem isoGaussian_lt_succ (hq : 2 ≤ q) {r k : ℕ} (hk : k + 1 < 2 * (r - k)) :
    isoGaussian r k q < isoGaussian r (k + 1) q := by
  have hpos := isoGaussian_pos hq (r := r) (k := k) (by omega)
  have hd := pow_sub_one_pos hq (m := k + 1) (by omega)
  have hlt : (q : ℚ) ^ (k + 1) - 1 < (q : ℚ) ^ (2 * (r - k)) - 1 := by
    have h1 : (1 : ℚ) < q := by exact_mod_cast hq
    have := pow_lt_pow_right₀ h1 hk
    linarith
  rw [isoGaussian_succ]
  calc isoGaussian r k q = isoGaussian r k q * 1 := (mul_one _).symm
    _ < _ := mul_lt_mul_of_pos_left ((one_lt_div hd).2 hlt) hpos

theorem isoGaussian_succ_le (hq : 2 ≤ q) {r k : ℕ} (hkr : k < r) (hk : 2 * (r - k) ≤ k + 1) :
    isoGaussian r (k + 1) q ≤ isoGaussian r k q := by
  have hpos := isoGaussian_pos hq (r := r) (k := k) hkr.le
  have hd := pow_sub_one_pos hq (m := k + 1) (by omega)
  have hle : (q : ℚ) ^ (2 * (r - k)) - 1 ≤ (q : ℚ) ^ (k + 1) - 1 := by
    have h1 : (1 : ℚ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have := pow_le_pow_right₀ h1 hk
    linarith
  rw [isoGaussian_succ]
  calc isoGaussian r k q * (((q : ℚ) ^ (2 * (r - k)) - 1) / ((q : ℚ) ^ (k + 1) - 1))
      ≤ isoGaussian r k q * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 hle) hpos.le
    _ = isoGaussian r k q := mul_one _

theorem isoGaussian_two_le (hq : 2 ≤ q) {r : ℕ} :
    ∀ k, 2 ≤ k → k ≤ r → 3 * k ≤ 2 * r + 2 → isoGaussian r 2 q ≤ isoGaussian r k q := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _ _; exact le_rfl
  | succ k hk ih =>
    intro hkr h3
    exact (ih (by omega) (by omega)).trans (isoGaussian_le_succ hq (by omega))

theorem isoGaussian_self_le (hq : 2 ≤ q) {r : ℕ} :
    ∀ n k, k + n = r → 2 * r + 3 ≤ 3 * k → isoGaussian r r q ≤ isoGaussian r k q := by
  intro n
  induction n with
  | zero => intro k hk _; rw [← hk, add_zero]
  | succ n ih =>
    intro k hk h3
    exact (ih (k + 1) (by omega) (by omega)).trans (isoGaussian_succ_le hq (by omega) (by omega))

theorem pow_le_prod_pow_add_one (hq : 2 ≤ q) {r : ℕ} (hr : 3 ≤ r) :
    (q : ℚ) ^ (2 * r) ≤ ∏ j ∈ range r, ((q : ℚ) ^ (j + 1) + 1) := by
  have h0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have h1 : (1 : ℚ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  induction r, hr using Nat.le_induction with
  | base =>
    calc (q : ℚ) ^ (2 * 3) = ∏ j ∈ range 3, (q : ℚ) ^ (j + 1) := by
          simp only [prod_range_succ, prod_range_zero]
          ring
      _ ≤ _ := prod_le_prod₀ (fun j _ => by positivity) fun j _ => by linarith
  | succ r hr ih =>
    rw [prod_range_succ, show 2 * (r + 1) = 2 * r + 2 by ring, pow_add]
    have h2 : (q : ℚ) ^ 2 ≤ (q : ℚ) ^ (r + 1) + 1 := by
      have := pow_le_pow_right₀ h1 (show 2 ≤ r + 1 by omega)
      linarith
    exact mul_le_mul ih h2 (by positivity) (by positivity)

theorem isotropic_gaussian_minimum {q r : ℕ} (hq : 2 ≤ q) (hr : 3 ≤ r) {k : ℕ} (hk : 2 ≤ k)
    (hkr : k ≤ r) : isoGaussian r 1 q < isoGaussian r k q := by
  have h2 : isoGaussian r 1 q < isoGaussian r 2 q := isoGaussian_lt_succ hq (by omega)
  have hself : isoGaussian r 1 q < isoGaussian r r q := by
    have hq1 : (1 : ℚ) ≤ (q : ℚ) - 1 := by
      have : (2 : ℚ) ≤ q := by exact_mod_cast hq
      linarith
    have hnum : (0 : ℚ) ≤ (q : ℚ) ^ (2 * r) - 1 := (pow_sub_one_pos hq (by omega)).le
    calc isoGaussian r 1 q = ((q : ℚ) ^ (2 * r) - 1) / ((q : ℚ) - 1) := isoGaussian_one r q
      _ ≤ (q : ℚ) ^ (2 * r) - 1 := div_le_self hnum hq1
      _ < (q : ℚ) ^ (2 * r) := by linarith
      _ ≤ _ := (pow_le_prod_pow_add_one hq hr).trans (isoGaussian_self hq r).ge
  rcases le_or_gt (3 * k) (2 * r + 2) with h | h
  · exact h2.trans_le (isoGaussian_two_le hq k hk hkr h)
  · exact hself.trans_le (isoGaussian_self_le hq (r - k) k (by omega) (by omega))

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
