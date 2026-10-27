module

public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem eq_of_prime_dvd_pow {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ q ^ k) :
    p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)

theorem primes_M11 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 7920) :
    p = 5 ∨ p = 11 := by
  rw [show (7920 : ℕ) = 2 ^ 4 * (3 ^ 2 * (5 ^ 1 * 11 ^ 1)) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_M12 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 95040) :
    p = 5 ∨ p = 11 := by
  rw [show (95040 : ℕ) = 2 ^ 6 * (3 ^ 3 * (5 ^ 1 * 11 ^ 1)) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_M22 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 443520) :
    p = 5 ∨ p = 7 ∨ p = 11 := by
  rw [show (443520 : ℕ) = 2 ^ 7 * (3 ^ 2 * (5 ^ 1 * (7 ^ 1 * 11 ^ 1))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_M23 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 10200960) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  rw [show (10200960 : ℕ) = 2 ^ 7 * (3 ^ 2 * (5 ^ 1 * (7 ^ 1 * (11 ^ 1 *
      23 ^ 1)))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_M24 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 244823040) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  rw [show (244823040 : ℕ) = 2 ^ 10 * (3 ^ 3 * (5 ^ 1 * (7 ^ 1 * (11 ^ 1 *
      23 ^ 1)))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_J2 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 604800) :
    p = 5 ∨ p = 7 := by
  rw [show (604800 : ℕ) = 2 ^ 7 * (3 ^ 3 * (5 ^ 2 * 7 ^ 1)) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_J3 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 50232960) :
    p = 5 ∨ p = 17 ∨ p = 19 := by
  rw [show (50232960 : ℕ) = 2 ^ 7 * (3 ^ 5 * (5 ^ 1 * (17 ^ 1 * 19 ^ 1))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_J4 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 86775571046077562880) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 43 := by
  rw [show (86775571046077562880 : ℕ) = 2 ^ 21 * (3 ^ 3 * (5 ^ 1 * (7 ^ 1 * (11 ^ 3 * (23 ^ 1 *
      (29 ^ 1 * (31 ^ 1 * (37 ^ 1 * 43 ^ 1)))))))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_HS {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 44352000) :
    p = 5 ∨ p = 7 ∨ p = 11 := by
  rw [show (44352000 : ℕ) = 2 ^ 9 * (3 ^ 2 * (5 ^ 3 * (7 ^ 1 * 11 ^ 1))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_McL {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 898128000) :
    p = 5 ∨ p = 7 ∨ p = 11 := by
  rw [show (898128000 : ℕ) = 2 ^ 7 * (3 ^ 6 * (5 ^ 3 * (7 ^ 1 * 11 ^ 1))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_He {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 4030387200) :
    p = 5 ∨ p = 7 ∨ p = 17 := by
  rw [show (4030387200 : ℕ) = 2 ^ 10 * (3 ^ 3 * (5 ^ 2 * (7 ^ 3 * 17 ^ 1))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_Ru {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 145926144000) :
    p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 29 := by
  rw [show (145926144000 : ℕ) = 2 ^ 14 * (3 ^ 3 * (5 ^ 3 * (7 ^ 1 * (13 ^ 1 *
      29 ^ 1)))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_Suz {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 448345497600) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  rw [show (448345497600 : ℕ) = 2 ^ 13 * (3 ^ 7 * (5 ^ 2 * (7 ^ 1 * (11 ^ 1 *
      13 ^ 1)))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_ON {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 460815505920) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 ∨ p = 31 := by
  rw [show (460815505920 : ℕ) = 2 ^ 9 * (3 ^ 4 * (5 ^ 1 * (7 ^ 3 * (11 ^ 1 * (19 ^ 1 *
      31 ^ 1))))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_Co2 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 42305421312000) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  rw [show (42305421312000 : ℕ) = 2 ^ 18 * (3 ^ 6 * (5 ^ 3 * (7 ^ 1 * (11 ^ 1 *
      23 ^ 1)))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_Co3 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 495766656000) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  rw [show (495766656000 : ℕ) = 2 ^ 10 * (3 ^ 7 * (5 ^ 3 * (7 ^ 1 * (11 ^ 1 *
      23 ^ 1)))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_HN {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 273030912000000) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
  rw [show (273030912000000 : ℕ) = 2 ^ 14 * (3 ^ 6 * (5 ^ 6 * (7 ^ 1 * (11 ^ 1 *
      19 ^ 1)))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_Ly {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 51765179004000000) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 31 ∨ p = 37 ∨ p = 67 := by
  rw [show (51765179004000000 : ℕ) = 2 ^ 8 * (3 ^ 7 * (5 ^ 6 * (7 ^ 1 * (11 ^ 1 * (31 ^ 1 *
      (37 ^ 1 * 67 ^ 1)))))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

theorem primes_Th {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ∣ 90745943887872000) :
    p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 19 ∨ p = 31 := by
  rw [show (90745943887872000 : ℕ) = 2 ^ 15 * (3 ^ 10 * (5 ^ 3 * (7 ^ 2 * (13 ^ 1 * (19 ^ 1 *
      31 ^ 1))))) by norm_num] at h
  repeat rw [Nat.Prime.dvd_mul hp] at h
  rcases h with h | h | h | h | h | h | h
  all_goals (have := eq_of_prime_dvd_pow hp (by norm_num) h; omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

end
