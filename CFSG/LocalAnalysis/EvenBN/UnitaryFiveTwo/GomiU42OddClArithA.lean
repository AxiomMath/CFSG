module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOrd

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem u42_arithA_three_le_pow {f : ℕ} (hf : 1 ≤ f) : 3 ≤ 3 ^ f :=
  calc (3 : ℕ) = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem u42_arithA_not_three_dvd_sub_one {f : ℕ} (hf : 1 ≤ f) : ¬ 3 ∣ 3 ^ f - 1 := by
  have h := u42_not_three_dvd_pow_sub_one (i := 1) hf le_rfl
  rwa [pow_one] at h

theorem u42_arithA_v3_mul_pow (n k : ℕ) (hn : ¬ 3 ∣ n) : (3 ^ k * n).factorization 3 = k := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero k (by norm_num : (3 : ℕ) ≠ 0)) hn0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hn, add_zero]

theorem u42_arithA_v3_C0 {C₀ : ℕ} (hC₀ : C₀ = 25920 ∨ C₀ = 51840) :
    C₀.factorization 3 = 4 := by
  rcases hC₀ with rfl | rfl
  · have h := u42_arithA_v3_mul_pow 320 4 (by norm_num)
    rwa [show (3 : ℕ) ^ 4 * 320 = 25920 by norm_num] at h
  · have h := u42_arithA_v3_mul_pow 640 4 (by norm_num)
    rwa [show (3 : ℕ) ^ 4 * 640 = 51840 by norm_num] at h

theorem u42_arithA_v3_e {f n e : ℕ} (hf : 1 ≤ f) (he : e ∣ Nat.gcd n (3 ^ f - 1)) :
    e.factorization 3 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro h3
  exact u42_arithA_not_three_dvd_sub_one hf (dvd_trans h3 (dvd_trans he (Nat.gcd_dvd_right _ _)))

theorem u42_arithA_v3_sub_one {f : ℕ} (hf : 1 ≤ f) : (3 ^ f - 1).factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (u42_arithA_not_three_dvd_sub_one hf)

theorem u42_arithA_v3_eps {ε : ℕ} (hε : ε = 1 ∨ ε = 2) : ε.factorization 3 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  rcases hε with rfl | rfl <;> norm_num

theorem u42_arithA_GL_ne_zero {q k : ℕ} (hq : 1 < q) : u42GL q k ≠ 0 := by
  unfold u42GL
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have h1 : q ^ i < q ^ k := Nat.pow_lt_pow_right hq (Finset.mem_range.mp hi)
  omega

theorem u42_arith_psl_split {f r s ε e C₀ : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hε : ε = 1 ∨ ε = 2) (hC₀ : C₀ = 25920 ∨ C₀ = 51840)
    (he : e ∣ Nat.gcd (r + s) (3 ^ f - 1))
    (h : C₀ * e * (3 ^ f - 1) = ε * (u42GL (3 ^ f) r * u42GL (3 ^ f) s)) : False := by
  have hq : 3 ≤ 3 ^ f := u42_arithA_three_le_pow hf
  have hq1 : 3 ^ f - 1 ≠ 0 := by omega
  have hC0 : C₀ ≠ 0 := by rcases hC₀ with rfl | rfl <;> norm_num
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hGLr : u42GL (3 ^ f) r ≠ 0 := u42_arithA_GL_ne_zero (by omega)
  have hGLs : u42GL (3 ^ f) s ≠ 0 := u42_arithA_GL_ne_zero (by omega)
  have he0 : e ≠ 0 := by
    rintro rfl
    have h1 := Nat.gcd_eq_zero_iff.mp (Nat.eq_zero_of_zero_dvd he)
    omega
  have he_le : e ≤ r + s := Nat.le_of_dvd (by omega) (dvd_trans he (Nat.gcd_dvd_left _ _))
  have hv : (C₀ * e * (3 ^ f - 1)).factorization 3
      = (ε * (u42GL (3 ^ f) r * u42GL (3 ^ f) s)).factorization 3 := by
    rw [h]
  rw [Nat.factorization_mul (mul_ne_zero hC0 he0) hq1, Nat.factorization_mul hC0 he0,
    Nat.factorization_mul hε0 (mul_ne_zero hGLr hGLs), Nat.factorization_mul hGLr hGLs] at hv
  simp only [Finsupp.add_apply] at hv
  rw [u42_arithA_v3_C0 hC₀, u42_arithA_v3_e hf he, u42_arithA_v3_sub_one hf,
    u42_arithA_v3_eps hε, u42_factorization_three_u42GL hf,
    u42_factorization_three_u42GL hf] at hv
  have hkey : f * (r * (r - 1) / 2) + f * (s * (s - 1) / 2) = 4 := by omega
  have hA : r * (r - 1) / 2 ≤ 4 := by
    have h1 : r * (r - 1) / 2 ≤ f * (r * (r - 1) / 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hB : s * (s - 1) / 2 ≤ 4 := by
    have h1 : s * (s - 1) / 2 ≤ f * (s * (s - 1) / 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hr3 : r ≤ 3 := by
    by_contra hcon
    have h1 : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hs3 : s ≤ 3 := by
    by_contra hcon
    have h1 : 4 * 3 ≤ s * (s - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hf4 : f ≤ 4 := by
    have h1 : f ∣ f * (r * (r - 1) / 2) + f * (s * (s - 1) / 2) :=
      dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)
    rw [hkey] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  interval_cases r <;> interval_cases s <;> interval_cases f <;> (try omega) <;>
    (try norm_num [u42GL, Finset.prod_range_succ] at h he_le) <;>
    rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;> omega

theorem u42_arith_psl_quad {f m ε e C₀ : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hε : ε = 1 ∨ ε = 2) (hC₀ : C₀ = 25920 ∨ C₀ = 51840)
    (he : e ∣ Nat.gcd (2 * m) (3 ^ f - 1))
    (h : C₀ * e * (3 ^ f - 1) = ε * u42GL ((3 ^ f) ^ 2) m) : False := by
  have hq : 3 ≤ 3 ^ f := u42_arithA_three_le_pow hf
  have hq1 : 3 ^ f - 1 ≠ 0 := by omega
  have hC0 : C₀ ≠ 0 := by rcases hC₀ with rfl | rfl <;> norm_num
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hq2 : (3 ^ f) ^ 2 = 3 ^ (f * 2) := (pow_mul 3 f 2).symm
  rw [hq2] at h
  have hGL : u42GL (3 ^ (f * 2)) m ≠ 0 := u42_arithA_GL_ne_zero (by
    have : 3 ≤ 3 ^ (f * 2) := u42_arithA_three_le_pow (by omega)
    omega)
  have he0 : e ≠ 0 := by
    rintro rfl
    have h1 := Nat.gcd_eq_zero_iff.mp (Nat.eq_zero_of_zero_dvd he)
    omega
  have he_le : e ≤ 2 * m := Nat.le_of_dvd (by omega) (dvd_trans he (Nat.gcd_dvd_left _ _))
  have hv : (C₀ * e * (3 ^ f - 1)).factorization 3
      = (ε * u42GL (3 ^ (f * 2)) m).factorization 3 := by
    rw [h]
  rw [Nat.factorization_mul (mul_ne_zero hC0 he0) hq1, Nat.factorization_mul hC0 he0,
    Nat.factorization_mul hε0 hGL] at hv
  simp only [Finsupp.add_apply] at hv
  rw [u42_arithA_v3_C0 hC₀, u42_arithA_v3_e hf he, u42_arithA_v3_sub_one hf,
    u42_arithA_v3_eps hε, u42_factorization_three_u42GL (by omega : 1 ≤ f * 2)] at hv
  have hkey : f * 2 * (m * (m - 1) / 2) = 4 := by omega
  have hT : m * (m - 1) / 2 ≤ 4 := by
    have h1 : m * (m - 1) / 2 ≤ f * 2 * (m * (m - 1) / 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hm3 : m ≤ 3 := by
    by_contra hcon
    have h1 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hf2 : f ≤ 2 := by
    have h1 : f * 2 ∣ f * 2 * (m * (m - 1) / 2) := dvd_mul_right _ _
    rw [hkey] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    omega
  interval_cases m <;> interval_cases f <;> (try omega) <;>
    (try norm_num [u42GL, Finset.prod_range_succ] at h he_le) <;>
    rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;> omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
