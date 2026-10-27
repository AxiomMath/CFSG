module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

@[expose] def tailCount (q : ℚ) (r m k : ℕ) : ℚ :=
  (∏ j ∈ Finset.range k, ((q ^ (r - j) - 1) * (q ^ (r + m - j - 1) + 1))) /
    ∏ i ∈ Finset.Icc 1 k, (q ^ i - 1)

section Arith

variable {q : ℚ}

theorem tailCount_succ (r m k : ℕ) : tailCount q r m (k + 1) =
    tailCount q r m k * ((q ^ (r - k) - 1) * (q ^ (r + m - k - 1) + 1) / (q ^ (k + 1) - 1)) := by
  rw [tailCount, tailCount, Finset.prod_range_succ,
    Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
  exact mul_div_mul_comm _ _ _ _

variable (hq : 2 ≤ q)
include hq

theorem tailCount_pos {r m k : ℕ} (hk : k ≤ r) : 0 < tailCount q r m k := by
  refine div_pos (Finset.prod_pos fun j hj => mul_pos ?_ (pow_add_one_pos_of_two_le hq _))
    (Finset.prod_pos fun i hi => pow_sub_one_pos_of_two_le hq (Finset.mem_Icc.mp hi).1)
  rw [Finset.mem_range] at hj
  exact pow_sub_one_pos_of_two_le hq (by omega)

theorem tailCount_one (r m : ℕ) : tailCount q r m 1 = qNum q r * (q ^ (r + m - 1) + 1) := by
  have hq1 : q - 1 ≠ 0 := by linarith
  rw [tailCount, Finset.prod_range_one, Finset.Icc_self, Finset.prod_singleton, pow_one,
    Nat.sub_zero, Nat.sub_zero, ← qNum_mul_sub_one r]
  field_simp

theorem tailCount_self (r m : ℕ) : tailCount q r m r = ∏ j ∈ Finset.range r, (q ^ (m + j) + 1) := by
  have hN : ∏ j ∈ Finset.range r, (q ^ (r - j) - 1) = ∏ i ∈ Finset.Icc 1 r, (q ^ i - 1) := by
    rw [← Finset.prod_range_reflect (fun j => q ^ (r - j) - 1) r, prod_Icc_one_range]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show r - (r - 1 - j) = j + 1 by omega]
  have hP : ∏ j ∈ Finset.range r, (q ^ (r + m - j - 1) + 1) =
      ∏ j ∈ Finset.range r, (q ^ (m + j) + 1) := by
    rw [← Finset.prod_range_reflect (fun j => q ^ (r + m - j - 1) + 1) r]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show r + m - (r - 1 - j) - 1 = m + j by omega]
  have hD : ∏ i ∈ Finset.Icc 1 r, (q ^ i - 1) ≠ 0 :=
    (Finset.prod_pos fun i hi => pow_sub_one_pos_of_two_le hq (Finset.mem_Icc.mp hi).1).ne'
  rw [tailCount, Finset.prod_mul_distrib, hN, hP, mul_div_right_comm, div_self hD, one_mul]

theorem one_le_qNum {r : ℕ} (hr : 1 ≤ r) : 1 ≤ qNum q r := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [qNum, Finset.sum_range_succ', pow_zero]
  have : 0 ≤ ∑ i ∈ Finset.range n, q ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => pow_nonneg (by linarith) _
  linarith

theorem qNum_lt_prod_pow_succ_add_one {n : ℕ} (hn : 2 ≤ n) :
    qNum q (n + 1) < ∏ j ∈ Finset.range n, (q ^ (j + 1) + 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [qNum, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
      Finset.prod_range_zero]
    norm_num
    nlinarith [mul_pos (by linarith : (0 : ℚ) < q) (pow_pos (by linarith : (0 : ℚ) < q) 2)]
  | succ n hn ih =>
    rw [qNum, Finset.sum_range_succ, ← qNum, Finset.prod_range_succ]
    have h1 := one_le_qNum hq (r := n + 1) (by omega)
    have hpow : 0 < q ^ (n + 1) := pow_pos (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right h1 hpow.le]

theorem tailCount_one_lt_two {r m : ℕ} (hr : 3 ≤ r) : tailCount q r m 1 < tailCount q r m 2 := by
  have h2 : tailCount q r m 2 = tailCount q r m 1 *
      ((q ^ (r - 1) - 1) * (q ^ (r + m - 1 - 1) + 1) / (q ^ 2 - 1)) :=
    tailCount_succ r m 1
  rw [h2]
  refine lt_mul_of_one_lt_right (tailCount_pos hq (by omega)) ?_
  rw [one_lt_div (pow_sub_one_pos_of_two_le hq (by omega))]
  have h1 : q ^ 2 ≤ q ^ (r - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : 0 < q ^ (r + m - 1 - 1) := pow_pos (by linarith) _
  have h3 : 0 < q ^ 2 - 1 := pow_sub_one_pos_of_two_le hq (by omega)
  have h4 : 0 < q ^ (r - 1) - 1 := by linarith
  nlinarith [mul_pos h4 h2]

theorem tailCount_one_lt_self {r m : ℕ} (hr : 3 ≤ r) (hm : 1 ≤ m) :
    tailCount q r m 1 < tailCount q r m r := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [tailCount_one hq, tailCount_self hq, Finset.prod_range_succ,
    show n + 1 + m - 1 = m + n by omega]
  have hle : ∏ j ∈ Finset.range n, (q ^ (j + 1) + 1) ≤ ∏ j ∈ Finset.range n, (q ^ (m + j) + 1) :=
    Finset.prod_le_prod₀ (fun j _ => (pow_add_one_pos_of_two_le hq _).le) fun j _ => by
      have : q ^ (j + 1) ≤ q ^ (m + j) := pow_le_pow_right₀ (by linarith) (by omega)
      linarith
  have hlt := qNum_lt_prod_pow_succ_add_one hq (n := n) (by omega)
  exact mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt hle) (pow_add_one_pos_of_two_le hq _)

theorem tailRatio_anti {r m i j : ℕ} (hij : i < j) (hjr : j < r) :
    (q ^ (r - j) - 1) * (q ^ (r + m - j - 1) + 1) / (q ^ (j + 1) - 1) <
      (q ^ (r - i) - 1) * (q ^ (r + m - i - 1) + 1) / (q ^ (i + 1) - 1) := by
  have hq1 : 1 < q := by linarith
  have a1 : q ^ (r - j) < q ^ (r - i) := pow_lt_pow_right₀ hq1 (by omega)
  have a2 : q ^ (r + m - j - 1) < q ^ (r + m - i - 1) := pow_lt_pow_right₀ hq1 (by omega)
  have a3 : q ^ (i + 1) < q ^ (j + 1) := pow_lt_pow_right₀ hq1 (by omega)
  have p1 : 0 < q ^ (r - j) - 1 := pow_sub_one_pos_of_two_le hq (by omega)
  have p2 : 0 < q ^ (r + m - j - 1) + 1 := pow_add_one_pos_of_two_le hq _
  have p3 : 0 < q ^ (i + 1) - 1 := pow_sub_one_pos_of_two_le hq (by omega)
  have hnum : (q ^ (r - j) - 1) * (q ^ (r + m - j - 1) + 1) <
      (q ^ (r - i) - 1) * (q ^ (r + m - i - 1) + 1) := by nlinarith
  have hpos : 0 < (q ^ (r - i) - 1) * (q ^ (r + m - i - 1) + 1) := by nlinarith
  rw [div_lt_div_iff₀ (by linarith) p3]
  nlinarith

end Arith

theorem orthogonal_geometry_tail_count_comparison {q r m : ℕ} (hq : 2 ≤ q) (hr : 3 ≤ r)
    (hm : 1 ≤ m) :
    (∀ k, k ≤ r → 0 < tailCount q r m k) ∧
      ∀ k, 2 ≤ k → k ≤ r → tailCount q r m 1 < tailCount q r m k := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  refine ⟨fun k hk => tailCount_pos hq' hk, fun k hk2 hkr => ?_⟩
  have hmin := min_le_of_ratio_anti (a := tailCount q r m)
    (R := fun k => ((q : ℚ) ^ (r - k) - 1) * ((q : ℚ) ^ (r + m - k - 1) + 1) /
      ((q : ℚ) ^ (k + 1) - 1)) (m := 2) (n := r)
    (fun i _ hi => tailCount_pos hq' hi) (fun i => tailCount_succ r m i)
    (fun i j _ hij hjr => tailRatio_anti hq' hij hjr) hk2 hkr
  have h2 := tailCount_one_lt_two hq' (m := m) hr
  have hrr := tailCount_one_lt_self hq' hr hm
  exact lt_of_lt_of_le (lt_min h2 hrr) hmin

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
