module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Semidihedral.FixedCoreNontrivialPrimes

theorem lt_four_mul_add_six_of_eq {q f F : ℤ} (hq : 7 ≤ q) (hf : 0 < f) (hF : 1 < F)
    (h : f * (f + 1) * (q + 1) * (F - 1) ^ 2 = 2 * q * F * (F + 1) * (f - q) ^ 2) :
    f < 4 * q + 6 := by
  have hFF : 0 < F * (F + 1) := by positivity
  have hlt : (F - 1) ^ 2 < F * (F + 1) := by nlinarith
  have hpos : 0 < f * (f + 1) * (q + 1) := by positivity
  have hkey : 2 * q * (f - q) ^ 2 < f * (f + 1) * (q + 1) := by
    by_contra hcon
    push Not at hcon
    have h1 : f * (f + 1) * (q + 1) * (F - 1) ^ 2 < f * (f + 1) * (q + 1) * (F * (F + 1)) :=
      mul_lt_mul_of_pos_left hlt hpos
    have h2 : f * (f + 1) * (q + 1) * (F * (F + 1)) ≤ 2 * q * (f - q) ^ 2 * (F * (F + 1)) :=
      mul_le_mul_of_nonneg_right hcon hFF.le
    nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon (by linarith : (0 : ℤ) ≤ q - 1)]

theorem lt_four_mul_of_eq {q f F : ℤ} (hq : 7 ≤ q) (hf : 1 < f) (hF : 1 < F)
    (h : f * (f - 1) * (q - 1) * (F - 1) ^ 2 = 2 * q * F * (F + 1) * (f - q) ^ 2) :
    f < 4 * q := by
  have hFF : 0 < F * (F + 1) := by positivity
  have hlt : (F - 1) ^ 2 < F * (F + 1) := by nlinarith
  have hf1 : 0 < f - 1 := by linarith
  have hpos : 0 < f * (f - 1) * (q - 1) := by
    have : 0 < q - 1 := by linarith
    positivity
  have hkey : 2 * q * (f - q) ^ 2 < f * (f - 1) * (q - 1) := by
    by_contra hcon
    push Not at hcon
    have h1 : f * (f - 1) * (q - 1) * (F - 1) ^ 2 < f * (f - 1) * (q - 1) * (F * (F + 1)) :=
      mul_lt_mul_of_pos_left hlt hpos
    have h2 : f * (f - 1) * (q - 1) * (F * (F + 1)) ≤ 2 * q * (f - q) ^ 2 * (F * (F + 1)) :=
      mul_le_mul_of_nonneg_right hcon hFF.le
    nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon (by linarith : (0 : ℤ) ≤ q + 1)]

theorem eq_plus_false {q f F : ℤ} (hq : 1 ≤ q) (hf : 0 < f) (hF : 1 < F)
    (h : f * (f + 1) * (q - 1) * (F - 1) ^ 2 = 2 * q * F * (F + 1) * (f + q) ^ 2) : False := by
  have h1 : f * (f + 1) < (f + q) ^ 2 := by nlinarith
  have h2 : (q - 1) * (F - 1) ^ 2 < 2 * q * (F * (F + 1)) := by nlinarith
  have hA : 0 ≤ f * (f + 1) := by positivity
  have hB : 0 ≤ (q - 1) * (F - 1) ^ 2 := by
    have : 0 ≤ q - 1 := by linarith
    positivity
  have h3 : f * (f + 1) * ((q - 1) * (F - 1) ^ 2) < (f + q) ^ 2 * (2 * q * (F * (F + 1))) :=
    mul_lt_mul'' h1 h2 hA hB
  nlinarith

theorem delta_three_pos_false {q e f F : ℤ} (hq : 11 ≤ q) (he : e = 1 ∨ e = -1)
    (hf : q ^ 2 < f) (hF : 2 * q ^ 2 - 1 < F)
    (h : f * (f - 1) * (q + e) * (F + 1) ^ 2 = 2 * q * F * (F - 1) * (f + e * q) ^ 2) :
    False := by
  have hq0 : 0 < q := by linarith
  have hq2 : 121 ≤ q ^ 2 := by nlinarith
  have hF0 : 0 < F := by linarith
  have hk : 4 * q + 3 < (q - 1) * F := by nlinarith
  have h3 : (q + 1) * (F + 1) ^ 2 < 2 * q * (F * (F - 1)) := by nlinarith [mul_pos hF0 hF0]
  have hF1 : 0 < (F + 1) ^ 2 := by
    have : 0 < F + 1 := by linarith
    positivity
  rcases he with rfl | rfl
  ·
    have h1 : f * (f - 1) < (f + q) ^ 2 := by nlinarith
    have hA : 0 ≤ f * (f - 1) := by nlinarith
    have h4 : f * (f - 1) * ((q + 1) * (F + 1) ^ 2) < (f + q) ^ 2 * (2 * q * (F * (F - 1))) :=
      mul_lt_mul'' h1 h3 hA (by positivity)
    nlinarith
  ·
    have h1 : (q - 1) * (f * (f - 1)) < (q + 1) * (f - q) ^ 2 := by
      have hm : 0 < f - q ^ 2 := by linarith
      nlinarith [mul_pos hm hm, mul_pos hm hq0]
    have hfq : 0 < (f - q) ^ 2 := by
      have : f - q ≠ 0 := by nlinarith
      positivity
    have h4 : (q - 1) * (f * (f - 1)) * (F + 1) ^ 2 < (q + 1) * (f - q) ^ 2 * (F + 1) ^ 2 :=
      mul_lt_mul_of_pos_right h1 hF1
    have h5 : (f - q) ^ 2 * ((q + 1) * (F + 1) ^ 2) < (f - q) ^ 2 * (2 * q * (F * (F - 1))) :=
      mul_lt_mul_of_pos_left h3 hfq
    nlinarith

theorem nine_false {q f : ℤ} (hq : 3 ≤ q) (hf : 0 < f) (h : f * (f + 1) = 9 * (f + q ^ 2)) :
    False := by
  have hsq : (f - 4) ^ 2 = 9 * q ^ 2 + 16 := by linear_combination h
  rcases le_or_gt (f - 4) (3 * q) with h1 | h1
  · nlinarith
  · have h2 : 3 * q + 1 ≤ f - 4 := by linarith
    nlinarith

theorem seventeen_false {q f : ℤ} (hq : 3 ≤ q) (hf : 0 < f) (hf' : f < 4 * q + 6)
    (h : f * (f + 1) = 17 * (f + q ^ 2)) : False := by
  have hsq : (f - 8) ^ 2 = 17 * q ^ 2 + 64 := by linear_combination h
  rcases le_or_gt 8 f with h1 | h1
  · nlinarith
  · nlinarith

theorem small_case_false {q f g F : ℤ} (hq : 11 ≤ q) (hf : 0 < f) (hg : 0 < g) (hF : 1 < F)
    (hfg : f * g = q ^ 2 * F) (hf' : f < 4 * q + 6) (hg' : g < 4 * q)
    (hFmod : F ≡ 1 [ZMOD 8]) (h : f * (f + 1) = F * (f + q ^ 2)) : False := by
  have hq0 : 0 < q := by linarith
  have hF19 : F < 19 := by
    have h1 : f * g < (4 * q + 6) * (4 * q) := by
      have := mul_lt_mul'' hf' hg' hf.le hg.le
      linarith
    nlinarith
  have hcases : F = 9 ∨ F = 17 := by
    rw [Int.ModEq] at hFmod
    omega
  rcases hcases with rfl | rfl
  · exact nine_false (by linarith) hf h
  · exact seventeen_false (by linarith) hf hf' h

theorem signed_degree_three_order_formulas_false {q e f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ}
    (hq : 11 ≤ q) (he : e = 1 ∨ e = -1)
    (hsign : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hf₁ : 1 < f₁) (hf₂ : 1 < f₂) (hf₃ : 1 < f₃)
    (hsum : 1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0) (hprod : f₁ * f₂ = q ^ 2 * f₃)
    (hc₃ : f₃ ≡ -δ₃ [ZMOD 8])
    (h₁ : f₁ * (f₁ + δ₁) * (q + e) * (f₃ + δ₃) ^ 2 =
      2 * q * f₃ * (f₃ - δ₃) * (f₁ - e * δ₁ * q) ^ 2)
    (h₂ : f₂ * (f₂ + δ₂) * (q - e) * (f₃ + δ₃) ^ 2 =
      2 * q * f₃ * (f₃ - δ₃) * (f₂ + e * δ₂ * q) ^ 2) :
    False := by
  have hq0 : 0 < q := by linarith
  rcases hsign with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    have hrel : (f₁ - q ^ 2) * (f₂ - q ^ 2) = q ^ 2 * (q ^ 2 - 1) := by
      linear_combination hprod + q ^ 2 * hsum
    have hq2 : 121 ≤ q ^ 2 := by nlinarith
    have hpos : 0 < q ^ 2 * (q ^ 2 - 1) := by
      have : 0 < q ^ 2 - 1 := by linarith
      positivity
    have hf₁q : q ^ 2 < f₁ := by
      by_contra hcon
      push Not at hcon
      rcases eq_or_lt_of_le hcon with heq | hlt
      · rw [heq, sub_self, zero_mul] at hrel
        linarith
      · have hf₂q : f₂ < q ^ 2 := by
          by_contra h'
          push Not at h'
          nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : f₁ - q ^ 2 ≤ 0)
            (by linarith : (0 : ℤ) ≤ f₂ - q ^ 2)]
        have h1 : (q ^ 2 - f₁) * (q ^ 2 - f₂) ≤ (q ^ 2 - 2) * (q ^ 2 - 2) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
        nlinarith
    have hf₂q : q ^ 2 < f₂ := by
      by_contra h'
      push Not at h'
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℤ) ≤ f₁ - q ^ 2)
        (by linarith : f₂ - q ^ 2 ≤ 0)]
    have hF : 2 * q ^ 2 - 1 < f₃ := by linarith
    have h₁' : f₁ * (f₁ - 1) * (q + e) * (f₃ + 1) ^ 2 =
        2 * q * f₃ * (f₃ - 1) * (f₁ + e * q) ^ 2 := by
      rw [show f₁ + -1 = f₁ - 1 by ring, show f₁ - e * -1 * q = f₁ + e * q by ring] at h₁
      exact h₁
    exact delta_three_pos_false hq he hf₁q hF h₁'
  ·
    have hrel : f₂ * (f₂ + 1) = f₃ * (f₂ + q ^ 2) := by
      have hf₁e : f₁ = f₂ + 1 - f₃ := by linarith
      rw [hf₁e] at hprod
      linear_combination hprod
    rcases he with rfl | rfl
    · have h₂' : f₂ * (f₂ + 1) * (q - 1) * (f₃ - 1) ^ 2 =
          2 * q * f₃ * (f₃ + 1) * (f₂ + q) ^ 2 := by
        rw [show f₃ + -1 = f₃ - 1 by ring, show f₃ - -1 = f₃ + 1 by ring,
          show f₂ + 1 * 1 * q = f₂ + q by ring] at h₂
        exact h₂
      exact eq_plus_false (by linarith) (by linarith) hf₃ h₂'
    · have h₂' : f₂ * (f₂ + 1) * (q + 1) * (f₃ - 1) ^ 2 =
          2 * q * f₃ * (f₃ + 1) * (f₂ - q) ^ 2 := by
        rw [show f₃ + -1 = f₃ - 1 by ring, show f₃ - -1 = f₃ + 1 by ring,
          show q - -1 = q + 1 by ring, show f₂ + -1 * 1 * q = f₂ - q by ring] at h₂
        exact h₂
      have h₁' : f₁ * (f₁ - 1) * (q - 1) * (f₃ - 1) ^ 2 =
          2 * q * f₃ * (f₃ + 1) * (f₁ - q) ^ 2 := by
        rw [show f₃ + -1 = f₃ - 1 by ring, show f₃ - -1 = f₃ + 1 by ring,
          show f₁ + -1 = f₁ - 1 by ring, show q + -1 = q - 1 by ring,
          show f₁ - -1 * -1 * q = f₁ - q by ring] at h₁
        exact h₁
      have hb₂ := lt_four_mul_add_six_of_eq (by linarith) (by linarith) hf₃ h₂'
      have hb₁ := lt_four_mul_of_eq (by linarith) hf₁ hf₃ h₁'
      have hmod : f₃ ≡ 1 [ZMOD 8] := by simpa using hc₃
      exact small_case_false hq (by linarith) (by linarith) hf₃ (by rw [mul_comm]; exact hprod)
        hb₂ hb₁ hmod hrel
  ·
    have hrel : f₁ * (f₁ + 1) = f₃ * (f₁ + q ^ 2) := by
      have hf₂e : f₂ = f₁ + 1 - f₃ := by linarith
      rw [hf₂e] at hprod
      linear_combination hprod
    rcases he with rfl | rfl
    · have h₁' : f₁ * (f₁ + 1) * (q + 1) * (f₃ - 1) ^ 2 =
          2 * q * f₃ * (f₃ + 1) * (f₁ - q) ^ 2 := by
        rw [show f₃ + -1 = f₃ - 1 by ring, show f₃ - -1 = f₃ + 1 by ring,
          show f₁ - 1 * 1 * q = f₁ - q by ring] at h₁
        exact h₁
      have h₂' : f₂ * (f₂ - 1) * (q - 1) * (f₃ - 1) ^ 2 =
          2 * q * f₃ * (f₃ + 1) * (f₂ - q) ^ 2 := by
        rw [show f₃ + -1 = f₃ - 1 by ring, show f₃ - -1 = f₃ + 1 by ring,
          show f₂ + -1 = f₂ - 1 by ring, show f₂ + 1 * -1 * q = f₂ - q by ring] at h₂
        exact h₂
      have hb₁ := lt_four_mul_add_six_of_eq (by linarith) (by linarith) hf₃ h₁'
      have hb₂ := lt_four_mul_of_eq (by linarith) hf₂ hf₃ h₂'
      have hmod : f₃ ≡ 1 [ZMOD 8] := by simpa using hc₃
      exact small_case_false hq (by linarith) (by linarith) hf₃ hprod hb₁ hb₂ hmod hrel
    · have h₁' : f₁ * (f₁ + 1) * (q - 1) * (f₃ - 1) ^ 2 =
          2 * q * f₃ * (f₃ + 1) * (f₁ + q) ^ 2 := by
        rw [show f₃ + -1 = f₃ - 1 by ring, show f₃ - -1 = f₃ + 1 by ring,
          show q + -1 = q - 1 by ring, show f₁ - -1 * 1 * q = f₁ + q by ring] at h₁
        exact h₁
      exact eq_plus_false (by linarith) (by linarith) hf₃ h₁'

theorem three_order_formulas_false {g c d q f₁ f₂ f₃ : ℕ} {e δ₁ δ₂ δ₃ : ℤ}
    (hq : 11 ≤ q) (he : e = 1 ∨ e = -1)
    (hsign : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hf₁ : 1 < f₁) (hf₂ : 1 < f₂) (hf₃ : 1 < f₃)
    (hsum : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0) (hprod : f₁ * f₂ = q ^ 2 * f₃)
    (hc₃ : (f₃ : ℤ) ≡ -δ₃ [ZMOD 8]) (hc : 0 < c) (hd : 0 < d)
    (hden₁ : (f₁ : ℚ) - e * δ₁ * q ≠ 0) (hden₂ : (f₂ : ℚ) + e * δ₂ * q ≠ 0)
    (hG₁ : (g : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
      ((f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2) * ((q + e) / q))
    (hG₂ : (g : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
      ((f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2) * ((q - e) / q))
    (hG₃ : (g : ℤ) * ((f₃ : ℤ) + δ₃) ^ 2 * (d : ℤ) ^ 2 =
      2 * (c : ℤ) ^ 3 * ((f₃ : ℤ) * (f₃ - δ₃))) : False := by
  have hq0 : (q : ℚ) ≠ 0 := by
    have : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    exact this.ne'
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc0 : (c : ℤ) ^ 3 ≠ 0 := pow_ne_zero 3 (by exact_mod_cast hc.ne')
  have hX₁ : (f₁ : ℚ) - δ₁ * e * q ≠ 0 := fun h => hden₁ (by linear_combination h)
  have hX₂ : (f₂ : ℚ) + δ₂ * e * q ≠ 0 := fun h => hden₂ (by linear_combination h)
  have e₁ : (g : ℚ) * (d : ℚ) ^ 2 * (((f₁ : ℚ) - e * δ₁ * q) ^ 2 * q) =
      (c : ℚ) ^ 3 * ((f₁ : ℚ) * (f₁ + δ₁) * (q + e)) := by
    rw [hG₁]
    field_simp
  have e₂ : (g : ℚ) * (d : ℚ) ^ 2 * (((f₂ : ℚ) + e * δ₂ * q) ^ 2 * q) =
      (c : ℚ) ^ 3 * ((f₂ : ℚ) * (f₂ + δ₂) * (q - e)) := by
    rw [hG₂]
    field_simp
  have e₁Z : (g : ℤ) * (d : ℤ) ^ 2 * (((f₁ : ℤ) - e * δ₁ * q) ^ 2 * q) =
      (c : ℤ) ^ 3 * ((f₁ : ℤ) * (f₁ + δ₁) * (q + e)) := by exact_mod_cast e₁
  have e₂Z : (g : ℤ) * (d : ℤ) ^ 2 * (((f₂ : ℤ) + e * δ₂ * q) ^ 2 * q) =
      (c : ℤ) ^ 3 * ((f₂ : ℤ) * (f₂ + δ₂) * (q - e)) := by exact_mod_cast e₂
  have h₁ : (f₁ : ℤ) * (f₁ + δ₁) * (q + e) * (f₃ + δ₃) ^ 2 =
      2 * q * f₃ * (f₃ - δ₃) * (f₁ - e * δ₁ * q) ^ 2 := by
    apply mul_left_cancel₀ hc0
    linear_combination (-((f₃ : ℤ) + δ₃) ^ 2) * e₁Z + ((q : ℤ) * ((f₁ : ℤ) - e * δ₁ * q) ^ 2) * hG₃
  have h₂ : (f₂ : ℤ) * (f₂ + δ₂) * (q - e) * (f₃ + δ₃) ^ 2 =
      2 * q * f₃ * (f₃ - δ₃) * (f₂ + e * δ₂ * q) ^ 2 := by
    apply mul_left_cancel₀ hc0
    linear_combination (-((f₃ : ℤ) + δ₃) ^ 2) * e₂Z + ((q : ℤ) * ((f₂ : ℤ) + e * δ₂ * q) ^ 2) * hG₃
  exact signed_degree_three_order_formulas_false (q := (q : ℤ)) (by exact_mod_cast hq) he hsign
    (by exact_mod_cast hf₁) (by exact_mod_cast hf₂) (by exact_mod_cast hf₃) hsum
    (by exact_mod_cast hprod) hc₃ h₁ h₂

end CFSG.Semidihedral.FixedCoreNontrivialPrimes
