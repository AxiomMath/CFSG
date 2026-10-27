module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOrd

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem u42_arithC_v3_pow_mul {k m : ℕ} (hm : ¬ 3 ∣ m) (hm0 : m ≠ 0) :
    (3 ^ k * m).factorization 3 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k (by norm_num : (3 : ℕ) ≠ 0)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem u42_arithC_v3_C₀ {C₀ : ℕ} (hC₀ : C₀ = 25920 ∨ C₀ = 51840) :
    C₀.factorization 3 = 4 := by
  rcases hC₀ with rfl | rfl
  · rw [show (25920 : ℕ) = 3 ^ 4 * 320 by norm_num]
    exact u42_arithC_v3_pow_mul (by norm_num) (by norm_num)
  · rw [show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num]
    exact u42_arithC_v3_pow_mul (by norm_num) (by norm_num)

theorem u42_arithC_not_three_dvd {f : ℕ} (hf : 1 ≤ f) : ¬ 3 ∣ 3 ^ f + 1 := by
  have h := u42_not_three_dvd_pow_add_one hf (le_refl 1)
  rwa [pow_one] at h

theorem u42_arithC_v3_zero_of_dvd {e m : ℕ} (hm : ¬ 3 ∣ m) (he : e ∣ m) :
    e.factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (fun h3 => hm (h3.trans he))

theorem u42_arithC_split_cases {f r s a b : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hf4 : f ≤ 4) (hr3 : r ≤ 3) (hs3 : s ≤ 3) (ha : a = r * (r - 1) / 2)
    (hb : b = s * (s - 1) / 2) (hsum : 4 = f * a + f * b) :
    (f = 1 ∧ r = 2 ∧ s = 3) ∨ (f = 1 ∧ r = 3 ∧ s = 2) ∨ (f = 2 ∧ r = 2 ∧ s = 2) ∨
      (f = 4 ∧ r = 1 ∧ s = 2) ∨ (f = 4 ∧ r = 2 ∧ s = 1) := by
  subst ha hb
  interval_cases f <;> interval_cases r <;> interval_cases s <;> omega

theorem u42_arith_psu_split {f r s ε e C₀ : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hn : 3 ≤ r + s) (hε : ε = 1 ∨ ε = 2) (hC₀ : C₀ = 25920 ∨ C₀ = 51840)
    (he : e ∣ Nat.gcd (r + s) (3 ^ f + 1))
    (h : C₀ * e * (3 ^ f + 1) = ε * (u42GU (3 ^ f) r * u42GU (3 ^ f) s)) : False := by
  have hC0 : C₀ ≠ 0 := by rcases hC₀ with rfl | rfl <;> norm_num
  have hd1 : ¬ 3 ∣ 3 ^ f + 1 := u42_arithC_not_three_dvd hf
  have hd0 : 3 ^ f + 1 ≠ 0 := by positivity
  have he_dvd : e ∣ 3 ^ f + 1 := he.trans (Nat.gcd_dvd_right _ _)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at he_dvd
    exact hd0 he_dvd
  have hP : C₀ * e * (3 ^ f + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hC0 he0) hd0
  have hRHS : ε * (u42GU (3 ^ f) r * u42GU (3 ^ f) s) ≠ 0 := by rw [← h]; exact hP
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul hRHS
  have hprod : u42GU (3 ^ f) r * u42GU (3 ^ f) s ≠ 0 := right_ne_zero_of_mul hRHS
  have hr0 : u42GU (3 ^ f) r ≠ 0 := left_ne_zero_of_mul hprod
  have hs0 : u42GU (3 ^ f) s ≠ 0 := right_ne_zero_of_mul hprod
  have hv : (C₀ * e * (3 ^ f + 1)).factorization 3
      = (ε * (u42GU (3 ^ f) r * u42GU (3 ^ f) s)).factorization 3 := by rw [h]
  have hL : (C₀ * e * (3 ^ f + 1)).factorization 3
      = C₀.factorization 3 + e.factorization 3 + (3 ^ f + 1).factorization 3 := by
    rw [Nat.factorization_mul (mul_ne_zero hC0 he0) hd0, Finsupp.add_apply,
      Nat.factorization_mul hC0 he0, Finsupp.add_apply]
  have hR : (ε * (u42GU (3 ^ f) r * u42GU (3 ^ f) s)).factorization 3
      = ε.factorization 3 + ((u42GU (3 ^ f) r).factorization 3
        + (u42GU (3 ^ f) s).factorization 3) := by
    rw [Nat.factorization_mul hε0 hprod, Finsupp.add_apply, Nat.factorization_mul hr0 hs0,
      Finsupp.add_apply]
  have hε3 : ε.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rcases hε with rfl | rfl <;> norm_num)
  have hsum : 4 = f * (r * (r - 1) / 2) + f * (s * (s - 1) / 2) := by
    rw [hL, hR, u42_factorization_three_u42GU hf r, u42_factorization_three_u42GU hf s,
      u42_arithC_v3_C₀ hC₀, u42_arithC_v3_zero_of_dvd hd1 he_dvd,
      Nat.factorization_eq_zero_of_not_dvd hd1, hε3] at hv
    omega
  obtain ⟨a, ha⟩ : ∃ a, a = r * (r - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = s * (s - 1) / 2 := ⟨_, rfl⟩
  rw [← ha, ← hb] at hsum
  have hfab : f * (a + b) = 4 := by rw [mul_add]; omega
  have hab1 : 1 ≤ a + b := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
    · rw [h0, mul_zero] at hfab
      omega
    · omega
  have hf4 : f ≤ 4 := by
    have h1 : f * 1 ≤ f * (a + b) := Nat.mul_le_mul (le_refl f) hab1
    omega
  have hab4 : a + b ≤ 4 := by
    have h1 : 1 * (a + b) ≤ f * (a + b) := Nat.mul_le_mul hf (le_refl _)
    omega
  have ha4 : a ≤ 4 := by omega
  have hb4 : b ≤ 4 := by omega
  have hr3 : r ≤ 3 := by
    by_contra hc
    have h1 : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hs3 : s ≤ 3 := by
    by_contra hc
    have h1 : 4 * 3 ≤ s * (s - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  rcases u42_arithC_split_cases hf hr hs hf4 hr3 hs3 ha hb hsum with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hV : u42GU (3 ^ 1) 2 * u42GU (3 ^ 1) 3 = 2322432 := by decide
    rw [hV] at h
    have he_le := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) he
    norm_num at he_le
    interval_cases e <;> rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      norm_num at h
  · have hV : u42GU (3 ^ 1) 3 * u42GU (3 ^ 1) 2 = 2322432 := by decide
    rw [hV] at h
    have he_le := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) he
    norm_num at he_le
    interval_cases e <;> rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      norm_num at h
  · have hV : u42GU (3 ^ 2) 2 * u42GU (3 ^ 2) 2 = 51840000 := by decide
    rw [hV] at h
    have he_le := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) he
    norm_num at he_le
    interval_cases e <;> rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      norm_num at h
  · have hV : u42GU (3 ^ 4) 1 * u42GU (3 ^ 4) 2 = 3572864640 := by decide
    rw [hV] at h
    have he_le := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) he
    norm_num at he_le
    interval_cases e <;> rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      norm_num at h
  · have hV : u42GU (3 ^ 4) 2 * u42GU (3 ^ 4) 1 = 3572864640 := by decide
    rw [hV] at h
    have he_le := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) he
    norm_num at he_le
    interval_cases e <;> rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      norm_num at h

theorem u42_arith_psu_quad {f l ε e C₀ : ℕ} (hf : 1 ≤ f) (hl : 2 ≤ l)
    (hε : ε = 1 ∨ ε = 2) (hC₀ : C₀ = 25920 ∨ C₀ = 51840)
    (he : e ∣ Nat.gcd (2 * l) (3 ^ f + 1))
    (h : C₀ * e * (3 ^ f + 1) = ε * u42GL ((3 ^ f) ^ 2) l) : False := by
  have hC0 : C₀ ≠ 0 := by rcases hC₀ with rfl | rfl <;> norm_num
  have hd1 : ¬ 3 ∣ 3 ^ f + 1 := u42_arithC_not_three_dvd hf
  have hd0 : 3 ^ f + 1 ≠ 0 := by positivity
  have he_dvd : e ∣ 3 ^ f + 1 := he.trans (Nat.gcd_dvd_right _ _)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at he_dvd
    exact hd0 he_dvd
  have hP : C₀ * e * (3 ^ f + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hC0 he0) hd0
  have hRHS : ε * u42GL ((3 ^ f) ^ 2) l ≠ 0 := by rw [← h]; exact hP
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul hRHS
  have hG : u42GL ((3 ^ f) ^ 2) l ≠ 0 := right_ne_zero_of_mul hRHS
  have hv : (C₀ * e * (3 ^ f + 1)).factorization 3
      = (ε * u42GL ((3 ^ f) ^ 2) l).factorization 3 := by rw [h]
  have hL : (C₀ * e * (3 ^ f + 1)).factorization 3
      = C₀.factorization 3 + e.factorization 3 + (3 ^ f + 1).factorization 3 := by
    rw [Nat.factorization_mul (mul_ne_zero hC0 he0) hd0, Finsupp.add_apply,
      Nat.factorization_mul hC0 he0, Finsupp.add_apply]
  have hR : (ε * u42GL ((3 ^ f) ^ 2) l).factorization 3
      = ε.factorization 3 + (u42GL ((3 ^ f) ^ 2) l).factorization 3 := by
    rw [Nat.factorization_mul hε0 hG, Finsupp.add_apply]
  have hGv : (u42GL ((3 ^ f) ^ 2) l).factorization 3 = f * 2 * (l * (l - 1) / 2) := by
    rw [← pow_mul]
    exact u42_factorization_three_u42GL (by omega) l
  have hε3 : ε.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rcases hε with rfl | rfl <;> norm_num)
  have hsum : 4 = f * 2 * (l * (l - 1) / 2) := by
    rw [hL, hR, hGv, u42_arithC_v3_C₀ hC₀, u42_arithC_v3_zero_of_dvd hd1 he_dvd,
      Nat.factorization_eq_zero_of_not_dvd hd1, hε3] at hv
    omega
  have hl1 : 1 ≤ l * (l - 1) / 2 := by
    have h1 : 2 * 1 ≤ l * (l - 1) := Nat.mul_le_mul hl (by omega)
    omega
  have hf2 : f ≤ 2 := by
    have h1 : f * 2 * 1 ≤ f * 2 * (l * (l - 1) / 2) := Nat.mul_le_mul (le_refl _) hl1
    omega
  have hl2 : l ≤ 2 := by
    by_contra hc
    have h1 : 3 * 2 ≤ l * (l - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : 1 * 2 * 3 ≤ f * 2 * (l * (l - 1) / 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl 2)) (by omega)
    omega
  interval_cases l
  interval_cases f
  · omega
  · have hV : u42GL ((3 ^ 2) ^ 2) 2 = 42508800 := by decide
    rw [hV] at h
    have he_le := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by norm_num)) he
    norm_num at he_le
    interval_cases e <;> rcases hC₀ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      norm_num at h

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
