module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNDig
public import Mathlib.Data.Int.Star

public section

namespace CFSG.GH74.GLS.Stage4.Rest

namespace Mix11cN

section Arith

theorem four_mul_le_two_pow {t : ℕ} (ht : 4 ≤ t) : 4 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem two_mul_le_two_pow {t : ℕ} (ht : 1 ≤ t) : 2 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem le_mul_pow_of_two_le {t c P : ℕ} (hP : 2 ≤ P) (hc : 1 ≤ c) : 2 ^ t ≤ c * P ^ t :=
  calc 2 ^ t ≤ P ^ t := Nat.pow_le_pow_left hP t
    _ = 1 * P ^ t := (one_mul _).symm
    _ ≤ c * P ^ t := Nat.mul_le_mul_right _ hc

theorem two_mul_le_mul_pow {t c P : ℕ} (ht : 1 ≤ t) (hP : 2 ≤ P) (hc : 1 ≤ c) :
    2 * t ≤ c * P ^ t :=
  (two_mul_le_two_pow ht).trans (le_mul_pow_of_two_le hP hc)

theorem arith_cases {t c P : ℕ} (ht : 1 ≤ t) (hP : 2 ≤ P) (hc : 1 ≤ c)
    (h1 : 2 * t < c * P ^ t) (h2 : c * P ^ t < 4 * t) :
    (t = 1 ∧ c = 1 ∧ P = 3) ∨ (t = 3 ∧ c = 1 ∧ P = 2) := by
  have ht3 : t ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ t := by omega
    have := (four_mul_le_two_pow h4).trans (le_mul_pow_of_two_le (t := t) hP hc)
    omega
  interval_cases t
  · simp only [pow_one] at h1 h2
    left
    have hc1 : c = 1 := by
      by_contra h
      have : 2 ≤ c := by omega
      nlinarith
    subst hc1
    refine ⟨rfl, rfl, by omega⟩
  · exfalso
    have hP2 : P ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ P := by omega
      have h9 : 9 ≤ P ^ 2 := by nlinarith
      have : P ^ 2 ≤ c * P ^ 2 := Nat.le_mul_of_pos_left _ hc
      omega
    have hP2' : P = 2 := by omega
    subst hP2'
    norm_num at h1 h2
    omega
  · right
    have hP2 : P ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ P := by omega
      have h27 : 27 ≤ P ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ P ^ 3 := Nat.pow_le_pow_left h3 3
      have : P ^ 3 ≤ c * P ^ 3 := Nat.le_mul_of_pos_left _ hc
      omega
    have hP2' : P = 2 := by omega
    subst hP2'
    norm_num at h1 h2
    refine ⟨rfl, by omega, rfl⟩

end Arith

section Shape

theorem exists_unique_digit {q r : ℕ} (hq : q.Prime) (f : ℕ → ℕ)
    (h : ∏ i ∈ Finset.range r, (f i + 1) = q) :
    ∃ j < r, f j + 1 = q ∧ ∀ i < r, i ≠ j → f i = 0 := by
  have hqd : q ∣ ∏ i ∈ Finset.range r, (f i + 1) := by rw [h]
  obtain ⟨j, hj, hqj⟩ := (Prime.dvd_finsetProd_iff hq.prime (fun i => f i + 1)).1 hqd
  have hjd : f j + 1 ∣ q := by
    rw [← h]
    exact Finset.dvd_prod_of_mem (fun i => f i + 1) hj
  have hjq : f j + 1 = q := Nat.dvd_antisymm hjd hqj
  refine ⟨j, Finset.mem_range.1 hj, hjq, fun i hi hij => ?_⟩
  have h1 : ∏ i ∈ (Finset.range r).erase j, (f i + 1) = 1 := by
    have h3 := Finset.mul_prod_erase (Finset.range r) (fun i => f i + 1) hj
    rw [h, hjq] at h3
    exact Nat.eq_of_mul_eq_mul_left hq.pos (by rw [h3, mul_one])
  have hd : f i + 1 ∣ ∏ i ∈ (Finset.range r).erase j, (f i + 1) :=
    Finset.dvd_prod_of_mem (fun i => f i + 1) (Finset.mem_erase.2 ⟨hij, Finset.mem_range.2 hi⟩)
  rw [h1] at hd
  have := Nat.le_of_dvd one_pos hd
  omega

variable {p : ℕ}

theorem shape_one (hp : 1 < p) {n A : ℕ} (hA : A < p ^ n)
    (h : ∏ i ∈ Finset.range n, (dg p A i + 1) = 3) : ∃ j < n, A = 2 * p ^ j := by
  obtain ⟨j, hj, hj3, hz⟩ := exists_unique_digit Nat.prime_three (fun i => dg p A i) h
  refine ⟨j, hj, (sum_dg hp hA).trans ?_⟩
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
  · have h2 : dg p A j = 2 := by omega
    rw [h2]
  · intro i hi hij
    rw [hz i (Finset.mem_range.1 hi) hij]
    simp

theorem shape_three (hp : 1 < p) {n r A : ℕ} (hA : A < p ^ n) (hn : n = r * 3)
    (hper : ∀ i, dg p A ((i + r) % n) = dg p A (i % n))
    (h : ∏ i ∈ Finset.range r, (dg p A i + 1) = 2) :
    ∃ j < r, A = (1 + p ^ r + p ^ (2 * r)) * p ^ j := by
  subst hn
  obtain ⟨j, hj, hj2, hz⟩ := exists_unique_digit Nat.prime_two (fun i => dg p A i) h
  refine ⟨j, hj, ?_⟩
  have hf : ∀ i, (fun i => dg p A (i % (r * 3))) (i + r) = (fun i => dg p A (i % (r * 3))) i :=
    hper
  have h1 : A = ∑ i ∈ Finset.range (r * 3), dg p A (i % (r * 3)) * p ^ i := by
    refine (sum_dg hp hA).trans (Finset.sum_congr rfl fun i hi => ?_)
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
  have h2 : ∑ i ∈ Finset.range r, dg p A (i % (r * 3)) * p ^ i = p ^ j := by
    have h3 : ∑ i ∈ Finset.range r, dg p A (i % (r * 3)) * p ^ i =
        ∑ i ∈ Finset.range r, dg p A i * p ^ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hi) (by omega : r ≤ r * 3))]
    rw [h3, Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
    · have h4 : dg p A j = 1 := by omega
      rw [h4, one_mul]
    · intro i hi hij
      rw [hz i (Finset.mem_range.1 hi) hij]
      simp
  have h5 := sum_range_period (p := p) (f := fun i => dg p A (i % (r * 3))) (r := r) hf 3
  rw [← h1, h2] at h5
  rw [h5]
  simp [Finset.sum_range_succ, mul_comm]

end Shape

end Mix11cN

end CFSG.GH74.GLS.Stage4.Rest
