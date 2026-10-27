module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResEData

public section

namespace CFSG.EvenSporadicStandard.M24Std

theorem gl12_eq : gl12 = 2 ^ 66 * 3 ^ 8 * 5 ^ 3 * 7 ^ 4 * 11 * 13 * 17 * 23 * 31 ^ 2 * 73 * 89 *
    127 := by
  norm_num [gl12, Finset.prod_range_succ]

theorem prime_mem_of_dvd_gl12 {p : ℕ} (hp : p.Prime) (h : p ∣ gl12) :
    p ∈ ({2, 3, 5, 7, 11, 13, 17, 23, 31, 73, 89, 127} : Finset ℕ) := by
  rw [gl12_eq] at h
  have key : ∀ q k : ℕ, q.Prime → p ∣ q ^ k → p = q := fun q k hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)
  have h' : p ∣ 2 ^ 66 ∨ p ∣ 3 ^ 8 ∨ p ∣ 5 ^ 3 ∨ p ∣ 7 ^ 4 ∨ p ∣ 11 ^ 1 ∨ p ∣ 13 ^ 1 ∨
      p ∣ 17 ^ 1 ∨ p ∣ 23 ^ 1 ∨ p ∣ 31 ^ 2 ∨ p ∣ 73 ^ 1 ∨ p ∣ 89 ^ 1 ∨ p ∣ 127 ^ 1 := by
    simpa only [Nat.Prime.dvd_mul hp, or_assoc, pow_one] using h
  rcases h' with h | h | h | h | h | h | h | h | h | h | h | h
  · simp [key 2 66 (by norm_num) h]
  · simp [key 3 8 (by norm_num) h]
  · simp [key 5 3 (by norm_num) h]
  · simp [key 7 4 (by norm_num) h]
  · simp [key 11 1 (by norm_num) h]
  · simp [key 13 1 (by norm_num) h]
  · simp [key 17 1 (by norm_num) h]
  · simp [key 23 1 (by norm_num) h]
  · simp [key 31 2 (by norm_num) h]
  · simp [key 73 1 (by norm_num) h]
  · simp [key 89 1 (by norm_num) h]
  · simp [key 127 1 (by norm_num) h]

theorem rank_le_of_not_dvd {e m : ℕ}
    (hnd : ∀ p ∈ ({3, 5, 7, 11, 13, 17, 23, 31, 73, 89, 127} : Finset ℕ),
      ¬ p ^ (m + 1) * e ∣ gl12) :
    ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * e ∣ gl12 → r ≤ m := by
  intro p r hp hp2 hdvd
  by_contra hrm
  have hr : m + 1 ≤ r := by omega
  have h1 : p ^ (m + 1) * e ∣ gl12 := (mul_dvd_mul_right (pow_dvd_pow p hr) e).trans hdvd
  have h2 : p ∣ gl12 := (dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero m)) e).trans h1
  have h3 := prime_mem_of_dvd_gl12 hp h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h3
  rcases h3 with rfl | h3
  · exact hp2 rfl
  · exact hnd p (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact h3) h1

theorem rank_A8 : ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * 20160 ∣ gl12 → r ≤ 6 := by
  apply rank_le_of_not_dvd
  rw [gl12_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  norm_num

theorem rank_U42 : ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * 25920 ∣ gl12 → r ≤ 4 := by
  apply rank_le_of_not_dvd
  rw [gl12_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  norm_num

theorem rank_L52 : ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * 9999360 ∣ gl12 → r ≤ 6 := by
  apply rank_le_of_not_dvd
  rw [gl12_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  norm_num

theorem rank_U52 : ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * 13685760 ∣ gl12 → r ≤ 4 := by
  apply rank_le_of_not_dvd
  rw [gl12_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  norm_num

theorem rank_Sp44 : ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * 979200 ∣ gl12 → r ≤ 6 := by
  apply rank_le_of_not_dvd
  rw [gl12_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  norm_num

end CFSG.EvenSporadicStandard.M24Std
