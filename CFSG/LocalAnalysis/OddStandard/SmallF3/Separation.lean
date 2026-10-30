module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Facts

public section

namespace CFSG.OddStandard.SmallF3

open CFSG.Blueprint CFSG.Open CFSG.OddStandard.SmallF3Interfaces

private theorem three_pow_dvd_ordA (n r : ℕ) (hn : 0 < n) :
    3 ^ (r * (n * (2 * n - 1))) ∣ ordA (2 * n - 1) (3 ^ r) := by
  have h2n : 2 * n - 1 + 1 = 2 * n := Nat.sub_add_cancel (by omega)
  have hdvd : Nat.gcd (2 * n) (3 ^ r - 1) ∣
      ∏ i ∈ Finset.Icc 2 (2 * n), ((3 ^ r) ^ i - 1) := by
    have h1 : Nat.gcd (2 * n) (3 ^ r - 1) ∣ 3 ^ r - 1 := Nat.gcd_dvd_right _ _
    have h2 : 3 ^ r - 1 ∣ (3 ^ r) ^ 2 - 1 :=
      ⟨3 ^ r + 1, by rw [mul_comm]; simpa using Nat.pow_two_sub_pow_two (3 ^ r) 1⟩
    have h3 : (3 ^ r) ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 (2 * n), ((3 ^ r) ^ i - 1) :=
      Finset.dvd_prod_of_mem (fun i => (3 ^ r) ^ i - 1)
        (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    exact h1.trans (h2.trans h3)
  unfold ordA
  rw [h2n]
  have hexp : (2 * n - 1) * (2 * n) / 2 = n * (2 * n - 1) := by
    have h : (2 * n - 1) * (2 * n) = (2 * n - 1) * n * 2 :=
      calc (2 * n - 1) * (2 * n)
          = (2 * n - 1) * 2 * n := (mul_assoc (2 * n - 1) 2 n).symm
        _ = (2 * n - 1) * n * 2 := Nat.mul_right_comm (2 * n - 1) 2 n
    rw [h, Nat.mul_div_cancel _ (by norm_num : 0 < 2), mul_comm]
  rw [hexp, Nat.mul_div_assoc _ hdvd, pow_mul 3 r (n * (2 * n - 1))]
  exact ⟨_, rfl⟩

private theorem three_pow_dvd_ordTwistedA (n r : ℕ) (hn : 0 < n) :
    3 ^ (r * (n * (2 * n - 1))) ∣ ordTwistedA (2 * n - 1) (3 ^ r) := by
  have h2n : 2 * n - 1 + 1 = 2 * n := Nat.sub_add_cancel (by omega)
  have he2 : (((3 ^ r : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = (3 ^ r) ^ 2 - 1 := by
    have h1 : 1 ≤ (3 ^ r) ^ 2 := Nat.one_le_pow 2 (3 ^ r) (by positivity)
    have hcast : (((3 ^ r : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = (((3 ^ r) ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcast, Int.toNat_natCast]
  have hdvd : Nat.gcd (2 * n) (3 ^ r + 1) ∣
      ∏ i ∈ Finset.Icc 2 (2 * n), (((3 ^ r : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    have h1 : Nat.gcd (2 * n) (3 ^ r + 1) ∣ 3 ^ r + 1 := Nat.gcd_dvd_right _ _
    have h2 : 3 ^ r + 1 ∣ (3 ^ r) ^ 2 - 1 :=
      ⟨3 ^ r - 1, by simpa using Nat.pow_two_sub_pow_two (3 ^ r) 1⟩
    have h3 : (3 ^ r) ^ 2 - 1 ∣
        ∏ i ∈ Finset.Icc 2 (2 * n), (((3 ^ r : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
      rw [← he2]
      exact Finset.dvd_prod_of_mem
        (fun i => (((3 ^ r : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
        (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    exact h1.trans (h2.trans h3)
  unfold ordTwistedA
  rw [h2n]
  have hexp : (2 * n - 1) * (2 * n) / 2 = n * (2 * n - 1) := by
    have h : (2 * n - 1) * (2 * n) = (2 * n - 1) * n * 2 :=
      calc (2 * n - 1) * (2 * n)
          = (2 * n - 1) * 2 * n := (mul_assoc (2 * n - 1) 2 n).symm
        _ = (2 * n - 1) * n * 2 := Nat.mul_right_comm (2 * n - 1) 2 n
    rw [h, Nat.mul_div_cancel _ (by norm_num : 0 < 2), mul_comm]
  rw [hexp, Nat.mul_div_assoc _ hdvd, pow_mul 3 r (n * (2 * n - 1))]
  exact ⟨_, rfl⟩

private theorem not_three_pow_thirteen_dvd_of_mem_smallF3Orders {a : ℕ}
    (ha : a ∈ smallF3Orders) : ¬ 3 ^ 13 ∣ a := by
  simp only [smallF3Orders, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [Nat.dvd_iff_mod_eq_zero] <;> decide +kernel

private theorem le_twelve_of_three_pow_dvd_mem_smallF3Orders {N a : ℕ}
    (ha : a ∈ smallF3Orders) (h : 3 ^ N ∣ a) : N ≤ 12 := by
  by_contra hN
  push Not at hN
  exact not_three_pow_thirteen_dvd_of_mem_smallF3Orders ha
    ((Nat.pow_dvd_pow 3 (by omega : 13 ≤ N)).trans h)

theorem eq_of_ordA_mem_smallF3Orders {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (h : ordA (2 * n - 1) (3 ^ r) ∈ smallF3Orders) : n = 2 ∧ r = 1 := by
  have hN : r * (n * (2 * n - 1)) ≤ 12 :=
    le_twelve_of_three_pow_dvd_mem_smallF3Orders h (three_pow_dvd_ordA n r hn)
  have hn2 : n ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h3 : 3 ≤ n := by omega
    have h5 : 5 ≤ 2 * n - 1 := by omega
    have h15 : 15 ≤ n * (2 * n - 1) := by simpa using Nat.mul_le_mul h3 h5
    have hle : n * (2 * n - 1) ≤ r * (n * (2 * n - 1)) :=
      calc n * (2 * n - 1) = 1 * (n * (2 * n - 1)) := (one_mul _).symm
        _ ≤ r * (n * (2 * n - 1)) := Nat.mul_le_mul_right _ hr
    omega
  have hr12 : r ≤ 12 := by
    have h1 : 1 ≤ n * (2 * n - 1) := by
      simpa using Nat.mul_le_mul hn (show 1 ≤ 2 * n - 1 by omega)
    calc r = r * 1 := (mul_one r).symm
      _ ≤ r * (n * (2 * n - 1)) := Nat.mul_le_mul_left r h1
      _ ≤ 12 := hN
  interval_cases n <;> interval_cases r
  all_goals
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd h (by decide +kernel)

theorem eq_of_ordTwistedA_mem_smallF3Orders {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (h : ordTwistedA (2 * n - 1) (3 ^ r) ∈ smallF3Orders) : n = 2 ∧ r = 1 := by
  have hN : r * (n * (2 * n - 1)) ≤ 12 :=
    le_twelve_of_three_pow_dvd_mem_smallF3Orders h (three_pow_dvd_ordTwistedA n r hn)
  have hn2 : n ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h3 : 3 ≤ n := by omega
    have h5 : 5 ≤ 2 * n - 1 := by omega
    have h15 : 15 ≤ n * (2 * n - 1) := by simpa using Nat.mul_le_mul h3 h5
    have hle : n * (2 * n - 1) ≤ r * (n * (2 * n - 1)) :=
      calc n * (2 * n - 1) = 1 * (n * (2 * n - 1)) := (one_mul _).symm
        _ ≤ r * (n * (2 * n - 1)) := Nat.mul_le_mul_right _ hr
    omega
  have hr12 : r ≤ 12 := by
    have h1 : 1 ≤ n * (2 * n - 1) := by
      simpa using Nat.mul_le_mul hn (show 1 ≤ 2 * n - 1 by omega)
    calc r = r * 1 := (mul_one r).symm
      _ ≤ r * (n * (2 * n - 1)) := Nat.mul_le_mul_left r h1
      _ ≤ 12 := hN
  interval_cases n <;> interval_cases r
  all_goals
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd h (by decide +kernel)

theorem eq_of_lieModel_psl {Q : Type} [Group Q] (hQ : SmallF3LieQuotient Q) {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) (h : LieModel Q .PSL (2 * n) 3 r) : n = 2 ∧ r = 1 := by
  have hc : Nat.card Q = ordA (2 * n - 1) (3 ^ r) :=
    (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num)
      (h.statedClassicalModel_of_ne_zero (by omega : 2 * n ≠ 0))).1 rfl
  exact eq_of_ordA_mem_smallF3Orders hn hr (by rw [← hc]; exact card_mem_smallF3Orders hQ)

theorem eq_of_lieModel_psu {Q : Type} [Group Q] (hQ : SmallF3LieQuotient Q) {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) (h : LieModel Q .PSU (2 * n) 3 r) : n = 2 ∧ r = 1 := by
  have hc : Nat.card Q = ordTwistedA (2 * n - 1) (3 ^ r) :=
    (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num)
      (h.statedClassicalModel_of_ne_zero (by omega : 2 * n ≠ 0))).2.1 rfl
  exact eq_of_ordTwistedA_mem_smallF3Orders hn hr (by rw [← hc]; exact card_mem_smallF3Orders hQ)

end CFSG.OddStandard.SmallF3
