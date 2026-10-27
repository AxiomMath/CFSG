module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem app_Tsp_mul_Tsp_smul_add_smul [CharP K 2] (hBN : BN.IsAlt) {a b : N} {c d : K}
    (p q : K) :
    (Tsp hBN a c * Tsp hBN b d).app (p • a + q • b) =
      (p + c * BN a b * q + c * d * BN a b ^ 2 * p) • a + (d * BN a b * p + q) • b := by
  have hba : BN b a = BN a b := by rw [← hBN.neg_eq a b, CharTwo.neg_eq]
  rw [Gsp.app_mul, Tsp_app hBN a c, Tsp_app hBN b d]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hBN.self_eq_zero, hba, mul_zero, add_zero]
  module

theorem pow_four_app_of_coeffs [CharP K 2] (g : Gsp BN) {a b : N} {A B C : K}
    (hAC : A * C = B)
    (hstep : ∀ p q : K, g.app (p • a + q • b) = (p + A * q + B * p) • a + (C * p + q) • b) :
    (g ^ 4).app a = (1 + B ^ 2 + B ^ 3 + B ^ 4) • a + (C * B ^ 3) • b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : g.app a = (1 + B) • a + C • b := by
    simpa only [one_smul, zero_smul, add_zero, mul_zero, mul_one] using hstep 1 0
  have e2 : g.app ((1 + B) • a + C • b) = (1 + B + B ^ 2) • a + (C * B) • b := by
    rw [hstep]
    linear_combination (norm := module) (hAC • a) + B • (h2 • a) + C • (h2 • b)
  have e3 : g.app ((1 + B + B ^ 2) • a + (C * B) • b) =
      (1 + B ^ 2 + B ^ 3) • a + (C * (1 + B ^ 2)) • b := by
    rw [hstep]
    linear_combination (norm := module) B • (hAC • a) + (B + B ^ 2) • (h2 • a) +
      (C * B) • (h2 • b)
  have e4 : g.app ((1 + B ^ 2 + B ^ 3) • a + (C * (1 + B ^ 2)) • b) =
      (1 + B ^ 2 + B ^ 3 + B ^ 4) • a + (C * B ^ 3) • b := by
    rw [hstep]
    linear_combination (norm := module) (1 + B ^ 2) • (hAC • a) + (B + B ^ 3) • (h2 • a) +
      (C + C * B ^ 2) • (h2 • b)
  have hpow : (g ^ 4).app a = g.app (g.app (g.app (g.app a))) := by
    simp only [pow_succ, pow_zero, one_mul, Gsp.app_mul]
  rw [hpow, e1, e2, e3, e4]

theorem Tsp_mul_Tsp_pow_four_ne_one [CharP K 2] (hBN : BN.IsAlt) {a b : N} (hab : BN a b ≠ 0)
    {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) : (Tsp hBN a c * Tsp hBN b d) ^ 4 ≠ 1 := by
  intro h4
  have hba : BN b a = BN a b := by rw [← hBN.neg_eq a b, CharTwo.neg_eq]
  have hA := pow_four_app_of_coeffs (Tsp hBN a c * Tsp hBN b d) (A := c * BN a b)
    (B := c * d * BN a b ^ 2) (C := d * BN a b) (by ring)
    (app_Tsp_mul_Tsp_smul_add_smul hBN)
  rw [h4, Gsp.app_one] at hA
  have hz := congrArg (fun x => BN x a) hA
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hBN.self_eq_zero, hba] at hz
  have hY : d * BN a b * (c * d * BN a b ^ 2) ^ 3 * BN a b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hd hab)
      (pow_ne_zero 3 (mul_ne_zero (mul_ne_zero hc hd) (pow_ne_zero 2 hab)))) hab
  apply hY
  linear_combination -hz

end CFSG.ClassicalGroups.Alternating
