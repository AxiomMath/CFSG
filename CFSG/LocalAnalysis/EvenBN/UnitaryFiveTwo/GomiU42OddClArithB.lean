module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOrd

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem u42_arithB_not_three_dvd_sub_one {g : ℕ} (hg : 1 ≤ g) : ¬ 3 ∣ 3 ^ g - 1 := by
  have h := u42_not_three_dvd_pow_sub_one (f := g) (i := 1) hg le_rfl
  rwa [pow_one] at h

theorem u42_arithB_not_three_dvd_sq_sub_one {g : ℕ} (hg : 1 ≤ g) :
    ¬ 3 ∣ 3 ^ (2 * g) - 1 := by
  have h := u42_not_three_dvd_pow_sub_one (f := g) (i := 2) hg (by norm_num)
  rwa [← pow_mul, mul_comm g 2] at h

theorem u42_arithB_factorization_three_pow_four_mul {m : ℕ} (hm : ¬ 3 ∣ m) (hm0 : m ≠ 0) :
    (3 ^ 4 * m).factorization 3 = 4 := by
  rw [Nat.factorization_mul (by positivity : (3 : ℕ) ^ 4 ≠ 0) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd hm,
    Finsupp.single_eq_same, add_zero]

theorem u42_arithB_solve {g n : ℕ} (hg : 1 ≤ g) (hn : 2 ≤ n)
    (h : g * (n * (n - 1) / 2) = 4) : n = 2 ∧ g = 4 := by
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · have h1 : 2 * (2 - 1) / 2 = 1 := by norm_num
    rw [h1, mul_one] at h
    exact ⟨rfl, h⟩
  · have h3 : 3 * (3 - 1) / 2 = 3 := by norm_num
    rw [h3] at h
    exfalso
    omega
  · have hT : 6 ≤ n * (n - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul h4 (by omega)
      omega
    have h6 : 1 * 6 ≤ g * (n * (n - 1) / 2) := Nat.mul_le_mul hg hT
    exfalso
    omega

theorem u42_arith_psl_field {g n e C₀ : ℕ} (hg : 1 ≤ g) (hn : 2 ≤ n)
    (hC₀ : C₀ = 25920 ∨ C₀ = 51840)
    (he : e ∣ Nat.gcd n (3 ^ (2 * g) - 1))
    (h : C₀ * e * (3 ^ g - 1) = u42GL (3 ^ g) n) : False := by
  have hg3 : 3 ≤ 3 ^ g := by
    calc (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hsub : 3 ^ g - 1 ≠ 0 := by omega
  have hdvd : e ∣ 3 ^ (2 * g) - 1 := dvd_trans he (Nat.gcd_dvd_right _ _)
  have h3e : ¬ 3 ∣ e := fun h3 => u42_arithB_not_three_dvd_sq_sub_one hg (dvd_trans h3 hdvd)
  have he0 : e ≠ 0 := by
    intro h0
    subst h0
    exact h3e (dvd_zero 3)
  have hC0 : C₀ ≠ 0 := by
    rcases hC₀ with rfl | rfl <;> norm_num
  have hv_C0 : C₀.factorization 3 = 4 := by
    rcases hC₀ with rfl | rfl
    · rw [show (25920 : ℕ) = 3 ^ 4 * 320 by norm_num]
      exact u42_arithB_factorization_three_pow_four_mul (by norm_num) (by norm_num)
    · rw [show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num]
      exact u42_arithB_factorization_three_pow_four_mul (by norm_num) (by norm_num)
  have h1 : (C₀ * e).factorization 3 = 4 := by
    rw [Nat.factorization_mul hC0 he0, Finsupp.add_apply, hv_C0,
      Nat.factorization_eq_zero_of_not_dvd h3e, add_zero]
  have h2 : (3 ^ g - 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (u42_arithB_not_three_dvd_sub_one hg)
  have hL : (C₀ * e * (3 ^ g - 1)).factorization 3 = 4 := by
    rw [Nat.factorization_mul (mul_ne_zero hC0 he0) hsub, Finsupp.add_apply, h1, h2, add_zero]
  have hkey : g * (n * (n - 1) / 2) = 4 := by
    rw [← u42_factorization_three_u42GL hg n, ← h]
    exact hL
  obtain ⟨rfl, rfl⟩ := u42_arithB_solve hg hn hkey
  have hU : u42GL (3 ^ 4) 2 = 42508800 := by
    norm_num [u42GL, Finset.prod_range_succ]
  rw [hU] at h
  norm_num at h
  rcases hC₀ with rfl | rfl <;> omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
