module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428GaloisUnits

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem eq_of_pow_three_eq_pow_three {k : Type*} [Field k] [Finite k]
    (hcop : Nat.Coprime 3 (Nat.card k - 1)) {a b : k} (h : a ^ 3 = b ^ 3) : a = b := by
  haveI : Fintype k := Fintype.ofFinite k
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 0 := by
      have h3 : b ^ 3 = 0 := by rw [← h]; simp
      exact (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).1 h3
    rw [hb]
  · have hb : b ≠ 0 := by
      rintro rfl
      have h3 : a ^ 3 = 0 := by simpa using h
      exact ha ((pow_eq_zero_iff (by norm_num : 3 ≠ 0)).1 h3)
    have hu : (a * b⁻¹) ^ 3 = 1 := by
      rw [mul_pow, h, inv_pow, mul_inv_cancel₀ (pow_ne_zero 3 hb)]
    have hdvd3 : orderOf (a * b⁻¹) ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hu
    have hdvd : orderOf (a * b⁻¹) ∣ Nat.card k - 1 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [Nat.card_eq_fintype_card] using
        FiniteField.pow_card_sub_one_eq_one (a * b⁻¹) (mul_ne_zero ha (inv_ne_zero hb))
    have h1 : orderOf (a * b⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd
    have h2 : a * b⁻¹ = 1 := orderOf_eq_one_iff.1 h1
    calc a = a * b⁻¹ * b := by rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
      _ = 1 * b := by rw [h2]
      _ = b := one_mul b


theorem coprime_three_two_pow_sub_one_of_odd {s : ℕ} (hs : Odd s) :
    Nat.Coprime 3 (2 ^ s - 1) := by
  have h3 : Nat.Prime 3 := by decide
  exact h3.coprime_iff_not_dvd.2 (three_not_dvd_two_pow_sub_one_of_odd hs)

end CFSG.LocalAnalysis.GLTheoremA
