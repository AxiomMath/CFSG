module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem mul_pow_dvd_mul_pow_of_le {e p m n : ℕ} (he : 0 < e) (hp : 1 < p)
    (h : e * p ^ m ≤ e * p ^ n) : e * p ^ m ∣ e * p ^ n := by
  have hmn : m ≤ n := by
    have : p ^ m ≤ p ^ n := Nat.le_of_mul_le_mul_left h he
    exact (Nat.pow_le_pow_iff_right hp).mp this
  exact mul_dvd_mul_left e (pow_dvd_pow p hmn)

theorem three_mul_le_of_mul_pow_lt {e p m n : ℕ} (hp : 3 ≤ p)
    (h : e * p ^ m < e * p ^ n) : 3 * (e * p ^ m) ≤ e * p ^ n := by
  have hp1 : 1 < p := by omega
  have hmn : m < n := by
    have : p ^ m < p ^ n := lt_of_mul_lt_mul_left h (Nat.zero_le e)
    exact (Nat.pow_lt_pow_iff_right hp1).mp this
  calc 3 * (e * p ^ m) = e * (3 * p ^ m) := by ring
    _ ≤ e * (p * p ^ m) := Nat.mul_le_mul_left e (Nat.mul_le_mul_right _ hp)
    _ = e * p ^ (m + 1) := by ring
    _ ≤ e * p ^ n := Nat.mul_le_mul_left e (Nat.pow_le_pow_right (le_of_lt hp1) hmn)

section Feit

variable {I : Type*} {p e : ℕ} {b d : I → ℕ}

theorem degree_pos (hp : 3 ≤ p) (he : 1 ≤ e) (hd : ∀ i, d i = e * p ^ b i) (i : I) :
    0 < d i := by
  rw [hd i]
  exact Nat.mul_pos he (Nat.pow_pos (by omega))

variable [Fintype I] {M dmin : ℕ}

theorem sq_dvd_sum_sq_filter_lt (hp : 3 ≤ p) (he : 1 ≤ e) (hd : ∀ i, d i = e * p ^ b i)
    (hdvd : ∀ i, d i ^ 2 ∣ M) (hMsum : M ∣ ∑ i, d i ^ 2) (j : I) :
    d j ^ 2 ∣ ∑ i ∈ Finset.univ.filter (fun i ↦ d i < d j), d i ^ 2 := by
  have hp1 : 1 < p := by omega
  have hsplit : (∑ i ∈ Finset.univ.filter (fun i ↦ d i < d j), d i ^ 2)
      + ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ d i < d j), d i ^ 2 = ∑ i, d i ^ 2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hdj2 : d j ^ 2 ∣ ∑ i, d i ^ 2 := (hdvd j).trans hMsum
  have hbig : d j ^ 2 ∣ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ d i < d j), d i ^ 2 := by
    refine Finset.dvd_sum fun i hi ↦ ?_
    have hle : d j ≤ d i := by simpa using (Finset.mem_filter.mp hi).2
    refine pow_dvd_pow_of_dvd ?_ 2
    rw [hd i, hd j] at hle ⊢
    exact mul_pow_dvd_mul_pow_of_le he hp1 hle
  have := Nat.dvd_sub hdj2 hbig
  rwa [← hsplit, Nat.add_sub_cancel] at this

theorem sum_sq_filter_lt_pos (hp : 3 ≤ p) (he : 1 ≤ e) (hd : ∀ i, d i = e * p ^ b i)
    (hmin : IsLeast (Set.range d) dmin) {j : I} (hj : dmin < d j) :
    0 < ∑ i ∈ Finset.univ.filter (fun i ↦ d i < d j), d i ^ 2 := by
  obtain ⟨i₀, hi₀⟩ := hmin.1
  have hmem : i₀ ∈ Finset.univ.filter (fun i ↦ d i < d j) := by simp [hi₀, hj]
  refine lt_of_lt_of_le (b := d i₀ ^ 2) (pow_pos (degree_pos hp he hd i₀) 2) ?_
  exact Finset.single_le_sum (f := fun i ↦ d i ^ 2) (fun i _ ↦ Nat.zero_le _) hmem

theorem two_mul_min_mul_lt_sum_sq_filter_lt (hp : 3 ≤ p) (he : 1 ≤ e)
    (hd : ∀ i, d i = e * p ^ b i) (hdvd : ∀ i, d i ^ 2 ∣ M) (hMsum : M ∣ ∑ i, d i ^ 2)
    (hmin : IsLeast (Set.range d) dmin) {j : I} (hj : dmin < d j) :
    2 * dmin * d j < ∑ i ∈ Finset.univ.filter (fun i ↦ d i < d j), d i ^ 2 := by
  obtain ⟨i₀, hi₀⟩ := hmin.1
  have hposW := sum_sq_filter_lt_pos hp he hd hmin hj
  have hle : d j ^ 2 ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ d i < d j), d i ^ 2 :=
    Nat.le_of_dvd hposW (sq_dvd_sum_sq_filter_lt hp he hd hdvd hMsum j)
  have h3 : 3 * dmin ≤ d j := by
    have h : e * p ^ b i₀ < e * p ^ b j := by rw [← hd i₀, ← hd j, hi₀]; exact hj
    have := three_mul_le_of_mul_pow_lt hp h
    rwa [← hd i₀, ← hd j, hi₀] at this
  have hdminpos : 0 < dmin := hi₀ ▸ degree_pos hp he hd i₀
  have hkey : 2 * dmin * d j < d j ^ 2 := by
    calc 2 * dmin * d j < 3 * dmin * d j :=
          Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl (d j)) (degree_pos hp he hd j)
      _ ≤ d j * d j := Nat.mul_le_mul_right _ h3
      _ = d j ^ 2 := by ring
  omega

end Feit

end CFSG.FeitThompson
