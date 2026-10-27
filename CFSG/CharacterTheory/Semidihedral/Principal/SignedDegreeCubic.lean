module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace CFSG.Semidihedral.Principal

theorem dvd_sq_sub_one_of_mul_eq {q m s c : ℤ} (hc : c * c = 1)
    (h : s * (q * m + c) = q ^ 2 - 1) : (q * m + c) ∣ m ^ 2 - 1 :=
  ⟨q * m - c - m ^ 2 * s, by linear_combination m ^ 2 * h + hc⟩

theorem eq_one_of_mul_eq {q m s c : ℤ} (hq : 3 ≤ q) (hc : c = 1 ∨ c = -1) (hm : 1 ≤ m)
    (hmq : m < q) (h : s * (q * m + c) = q ^ 2 - 1) : m = 1 := by
  have hcc : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hdvd := dvd_sq_sub_one_of_mul_eq hcc h
  have hnonneg : 0 ≤ m ^ 2 - 1 := by nlinarith
  have hlt : m ^ 2 - 1 < q * m + c := by rcases hc with rfl | rfl <;> nlinarith
  have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hlt hdvd
  nlinarith

theorem pattern_ab_cubic {q a b f₃ : ℤ} (hq : 3 ≤ q) (ha : 1 < a) (hf₃ : 1 < f₃)
    (hb : b = a + f₃ - 1) (hprod : a * b = q ^ 2 * f₃) (hdiv : q ^ 3 ∣ b) :
    b = q ^ 3 ∧ a = q ^ 2 - q + 1 ∧ f₃ = q * (q ^ 2 - q + 1) := by
  subst hb
  obtain ⟨m, hm⟩ := hdiv
  have hq0 : 0 < q := by linarith
  have hlt : a < q ^ 2 := by nlinarith
  have hf₃eq : f₃ = q * m * a := by
    have h1 : a * (q ^ 3 * m) = q ^ 2 * f₃ := by rw [← hm]; exact hprod
    have hq2 : q ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hq2
    linear_combination -h1
  have hm1 : 1 ≤ m := by
    by_contra hlt1
    push Not at hlt1
    have hm0 : m ≤ 0 := by omega
    have hqa : 0 ≤ q * a := by positivity
    have : f₃ ≤ 0 := by
      rw [hf₃eq]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hqa hm0]
    linarith
  have hs : (q ^ 2 - a) * (q * m + 1) = q ^ 2 - 1 := by
    have := hm
    rw [hf₃eq] at this
    linear_combination -this
  have hmq : m < q := by
    by_contra hge
    push Not at hge
    have hs1 : 1 ≤ q ^ 2 - a := by linarith
    have hqm : q ^ 2 + 1 ≤ q * m + 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℤ) ≤ q * m + 1)
    linarith
  have hm_eq := eq_one_of_mul_eq hq (Or.inl rfl) hm1 hmq hs
  subst hm_eq
  have hsval : q ^ 2 - a = q - 1 := by
    have hq1 : q + 1 ≠ 0 := by linarith
    apply mul_right_cancel₀ hq1
    linear_combination hs
  refine ⟨?_, by linarith, ?_⟩
  · rw [hf₃eq] at hm; nlinarith
  · rw [hf₃eq]; nlinarith

theorem pattern_c_cubic {q a b f₃ : ℤ} (hq : 3 ≤ q) (hqodd : Odd q) (ha : 1 < a) (hb : 1 < b)
    (hbodd : Odd b)
    (hf₃ : f₃ = a + b - 1) (hprod : a * b = q ^ 2 * f₃) (hdiv : q ^ 3 ∣ a) :
    a = q ^ 3 ∧ b = q ^ 2 + q + 1 ∧ f₃ = q * (q ^ 2 + q + 1) := by
  subst hf₃
  obtain ⟨m, hm⟩ := hdiv
  have hq0 : 0 < q := by linarith
  have hfac : (a - q ^ 2) * (b - q ^ 2) = q ^ 2 * (q ^ 2 - 1) := by linarith
  have hapos : q ^ 2 < a := by
    by_contra hle
    push Not at hle
    have hlt₁ : a < q ^ 2 := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · rw [h, sub_self, zero_mul] at hfac
        have : 0 < q ^ 2 * (q ^ 2 - 1) := by nlinarith
        linarith
    have hlt₂ : b < q ^ 2 := by
      by_contra hge
      push Not at hge
      nlinarith
    nlinarith
  have hbpos : q ^ 2 < b := by nlinarith
  have hq3 : 0 < q ^ 3 := pow_pos hq0 3
  have hm1 : 1 ≤ m := by
    by_contra hlt1
    push Not at hlt1
    have : q ^ 3 * m ≤ 0 := by nlinarith
    linarith
  have hs : (b - q ^ 2) * (q * m - 1) = q ^ 2 - 1 := by
    have hq2 : q ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hq2
    rw [hm] at hfac
    linear_combination hfac
  have hmq : m ≤ q := by
    by_contra hgt
    push Not at hgt
    have hs1 : 1 ≤ b - q ^ 2 := by linarith
    have hqm : q ^ 2 + q - 1 ≤ q * m - 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right hs1 (by nlinarith : (0 : ℤ) ≤ q * m - 1)
    nlinarith
  rcases lt_or_eq_of_le hmq with hlt | heq
  · have hm_eq := eq_one_of_mul_eq hq (c := -1) (Or.inr rfl) hm1 hlt
      (by rw [show q * m + -1 = q * m - 1 by ring]; exact hs)
    subst hm_eq
    have hbval : b - q ^ 2 = q + 1 := by
      have hq1 : q - 1 ≠ 0 := by linarith
      apply mul_right_cancel₀ hq1
      linear_combination hs
    refine ⟨by rw [hm]; ring, by linarith, by rw [hm]; nlinarith⟩
  · exfalso
    subst heq
    have hb1 : b - m ^ 2 = 1 := by
      have hne : m * m - 1 ≠ 0 := by nlinarith
      apply mul_right_cancel₀ hne
      linear_combination hs
    obtain ⟨c, hc⟩ : Odd (m ^ 2) := hqodd.pow
    obtain ⟨k, hk⟩ := hbodd
    generalize m ^ 2 = M2 at hc hb1
    omega

theorem lt_of_pattern_small {Q x y f : ℤ} (hx : 1 < x) (hf : 1 < f) (hy : y = x + f - 1)
    (hprod : x * y = Q * f) : x < Q := by
  subst hy
  have heq : x * (x - 1) = f * (Q - x) := by linear_combination hprod
  by_contra hle
  push Not at hle
  have h1 : f * (Q - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have h2 : 0 < x * (x - 1) := mul_pos (by linarith) (by linarith)
  linarith

theorem not_cube_dvd_of_lt {q x : ℤ} (hq : 3 ≤ q) (hx : 0 < x) (hlt : x < q ^ 2) :
    ¬ q ^ 3 ∣ x := by
  rintro ⟨m, hm⟩
  have hq0 : 0 < q := by linarith
  have hq2 : 0 < q ^ 2 := by positivity
  have hm1 : 1 ≤ m := by
    by_contra h
    push Not at h
    have : q ^ 3 * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    linarith
  have : q ^ 3 ≤ x := by
    rw [hm]
    nlinarith [pow_pos hq0 3]
  have : q ^ 2 < q ^ 3 := by
    rw [pow_succ]
    nlinarith
  linarith

theorem signed_degree_product_cubic_divisibility_rigidity (q e f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ)
    (hq : 3 ≤ q) (hqodd : Odd q) (he : q % 4 = 1 ∧ e = 1 ∨ q % 4 = 3 ∧ e = -1)
    (hf₁ : 1 < f₁) (hf₂ : 1 < f₂) (hf₃ : 1 < f₃) (ho₁ : Odd f₁) (ho₂ : Odd f₂) (ho₃ : Odd f₃)
    (hsigns : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hsum : 1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0) (hprod : f₁ * f₂ = q ^ 2 * f₃)
    (hc₁ : f₁ ≡ δ₁ * (2 - e * q) [ZMOD 8]) (hc₂ : f₂ ≡ -δ₂ * e * q [ZMOD 8])
    (hc₃ : f₃ ≡ -δ₃ [ZMOD 8]) (hdiv : q ^ 3 ∣ f₁ ∨ q ^ 3 ∣ f₂) :
    δ₁ = e ∧ δ₂ = -1 ∧ δ₃ = -e ∧ f₁ = q ^ 3 ∧ f₂ = q ^ 2 - e * q + 1 ∧
      f₃ = q * (q ^ 2 - e * q + 1) ∧ f₁ + δ₁ = q ^ 3 + e ∧ f₂ + δ₂ = q ^ 2 - e * q := by
  have hq0 : 0 < q := by linarith
  have hodd2 : q % 2 = 1 := Int.odd_iff.mp hqodd
  have hcast : ∀ r : ℤ, 0 ≤ r → r < 8 → q % 8 = r → (q : ZMod 8) = r := fun r h0 h8 hr =>
    (ZMod.intCast_eq_intCast_iff' q r 8).mpr (by rw [Nat.cast_ofNat]; omega)
  replace hc₁ := (ZMod.intCast_eq_intCast_iff' _ _ 8).mpr hc₁
  replace hc₂ := (ZMod.intCast_eq_intCast_iff' _ _ 8).mpr hc₂
  replace hc₃ := (ZMod.intCast_eq_intCast_iff' _ _ 8).mpr hc₃
  rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    rcases hdiv with hd | hd
    · obtain ⟨rfl, rfl, rfl⟩ := pattern_c_cubic hq hqodd hf₁ hf₂ ho₂ (by linarith) hprod hd
      rcases he with ⟨h4, rfl⟩ | ⟨h4, rfl⟩
      · exfalso
        push_cast at hc₁
        have h8 : q % 8 = 1 ∨ q % 8 = 5 := by omega
        rcases h8 with h | h <;> rw [hcast _ (by norm_num) (by norm_num) h] at hc₁ <;>
          revert hc₁ <;> decide
      · refine ⟨rfl, rfl, by norm_num, rfl, by ring, by ring, by ring, by ring⟩
    · obtain ⟨rfl, rfl, rfl⟩ := pattern_c_cubic (f₃ := f₃) hq hqodd hf₂ hf₁ ho₁ (by linarith)
        (by rw [mul_comm]; exact hprod) hd
      exfalso
      push_cast at hc₁
      rcases he with ⟨h4, rfl⟩ | ⟨h4, rfl⟩
      · have h8 : q % 8 = 1 ∨ q % 8 = 5 := by omega
        rcases h8 with h | h <;> rw [hcast _ (by norm_num) (by norm_num) h] at hc₁ <;>
          revert hc₁ <;> decide
      · have h8 : q % 8 = 3 ∨ q % 8 = 7 := by omega
        rcases h8 with h | h <;> rw [hcast _ (by norm_num) (by norm_num) h] at hc₁ <;>
          revert hc₁ <;> decide
  ·
    exfalso
    have hlt : f₁ < q ^ 2 := lt_of_pattern_small hf₁ hf₃ (by linarith) hprod
    rcases hdiv with hd | hd
    · exact not_cube_dvd_of_lt hq (by linarith) hlt hd
    · obtain ⟨rfl, rfl, rfl⟩ := pattern_ab_cubic hq hf₁ hf₃ (by linarith) hprod hd
      push_cast at hc₁ hc₂
      rcases he with ⟨h4, rfl⟩ | ⟨h4, rfl⟩
      · have h8 : q % 8 = 1 ∨ q % 8 = 5 := by omega
        rcases h8 with h | h <;> rw [hcast _ (by norm_num) (by norm_num) h] at hc₁ hc₂ <;>
          revert hc₁ hc₂ <;> decide
      · have h8 : q % 8 = 3 ∨ q % 8 = 7 := by omega
        rcases h8 with h | h <;> rw [hcast _ (by norm_num) (by norm_num) h] at hc₁ hc₂ <;>
          revert hc₁ hc₂ <;> decide
  ·
    have hlt : f₂ < q ^ 2 := lt_of_pattern_small (y := f₁) hf₂ hf₃ (by linarith)
      (by rw [mul_comm]; exact hprod)
    rcases hdiv with hd | hd
    · obtain ⟨rfl, rfl, rfl⟩ := pattern_ab_cubic (b := f₁) hq hf₂ hf₃ (by linarith)
        (by rw [mul_comm]; exact hprod) hd
      rcases he with ⟨h4, rfl⟩ | ⟨h4, rfl⟩
      · refine ⟨rfl, rfl, rfl, rfl, by ring, by ring, by ring, by ring⟩
      · exfalso
        push_cast at hc₁
        have h8 : q % 8 = 3 ∨ q % 8 = 7 := by omega
        rcases h8 with h | h <;> rw [hcast _ (by norm_num) (by norm_num) h] at hc₁ <;>
          revert hc₁ <;> decide
    · exact absurd hd (not_cube_dvd_of_lt hq (by linarith) hlt)

end CFSG.Semidihedral.Principal
