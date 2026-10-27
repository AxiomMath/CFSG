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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Semidihedral.Principal

theorem five_signed_degree_case_a {f₁ f₂ f₃ : ℤ} (hf₁ : 1 < f₁) (hf₃ : 1 < f₃)
    (hsum : 1 - f₁ + f₂ - f₃ = 0) (hprod : f₁ * f₂ = 25 * f₃) (hc₁ : f₁ ≡ 3 [ZMOD 16]) :
    f₁ = 19 ∧ f₂ = 75 ∧ f₃ = 57 := by
  have hf₂ : f₂ = f₁ + f₃ - 1 := by linarith
  subst hf₂
  have hlt : f₁ < 25 := by nlinarith
  rw [Int.ModEq] at hc₁
  interval_cases f₁ <;> omega

theorem five_signed_degree_case_b {f₁ f₂ f₃ : ℤ} (hf₂ : 1 < f₂) (hf₃ : 1 < f₃)
    (hsum : 1 + f₁ - f₂ - f₃ = 0) (hprod : f₁ * f₂ = 25 * f₃) (hc₂ : f₂ ≡ 5 [ZMOD 16]) :
    f₁ = 125 ∧ f₂ = 21 ∧ f₃ = 105 := by
  have hf₁ : f₁ = f₂ + f₃ - 1 := by linarith
  subst hf₁
  have hlt : f₂ < 25 := by nlinarith
  rw [Int.ModEq] at hc₂
  interval_cases f₂ <;> omega

theorem five_signed_degree_case_c {f₁ f₂ f₃ : ℤ} (hf₁ : 1 < f₁) (hf₂ : 1 < f₂)
    (hsum : 1 - f₁ - f₂ + f₃ = 0) (hprod : f₁ * f₂ = 25 * f₃) (hc₁ : f₁ ≡ 3 [ZMOD 16])
    (hc₂ : f₂ ≡ 5 [ZMOD 16]) :
    f₁ = 35 ∧ f₂ = 85 ∧ f₃ = 119 := by
  have hf₃ : f₃ = f₁ + f₂ - 1 := by linarith
  subst hf₃
  have hfac : (f₁ - 25) * (f₂ - 25) = 600 := by linarith
  have hpos₁ : 25 < f₁ := by
    by_contra hle
    push Not at hle
    have hlt₁ : f₁ < 25 := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · rw [h] at hfac; norm_num at hfac
    have hlt₂ : f₂ < 25 := by
      by_contra hge
      push Not at hge
      nlinarith
    nlinarith
  have hpos₂ : 25 < f₂ := by nlinarith
  have hle₁ : f₁ ≤ 625 := by nlinarith
  rw [Int.ModEq] at hc₁ hc₂
  interval_cases f₁ <;> omega

theorem five_signed_degree_product_three_alternatives :
    (∀ f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ, 1 < f₁ → 1 < f₂ → 1 < f₃ → Odd f₁ → Odd f₂ → Odd f₃ →
      ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
        (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) →
      1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0 → f₁ * f₂ = 25 * f₃ →
      f₁ ≡ -3 * δ₁ [ZMOD 16] → f₂ ≡ -5 * δ₂ [ZMOD 16] →
      ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, 1, -1), (19, 75, 57)) ∨
        ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((1, -1, -1), (125, 21, 105)) ∨
        ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, -1, 1), (35, 85, 119))) ∧
    (∀ δ₁ δ₂ δ₃ f₁ f₂ f₃ : ℤ,
      (((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, 1, -1), (19, 75, 57)) ∨
        ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((1, -1, -1), (125, 21, 105)) ∨
        ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, -1, 1), (35, 85, 119))) →
      1 < f₁ ∧ 1 < f₂ ∧ 1 < f₃ ∧ Odd f₁ ∧ Odd f₂ ∧ Odd f₃ ∧
      ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
        (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
      1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0 ∧ f₁ * f₂ = 25 * f₃ ∧
      f₁ ≡ -3 * δ₁ [ZMOD 16] ∧ f₂ ≡ -5 * δ₂ [ZMOD 16]) := by
  refine ⟨?_, ?_⟩
  · intro f₁ f₂ f₃ δ₁ δ₂ δ₃ hf₁ hf₂ hf₃ _ _ _ hsigns hsum hprod hc₁ hc₂
    rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := five_signed_degree_case_c hf₁ hf₂ (by linarith) hprod
        (by simpa using hc₁) (by simpa using hc₂)
      exact Or.inr (Or.inr rfl)
    · obtain ⟨rfl, rfl, rfl⟩ := five_signed_degree_case_a hf₁ hf₃ (by linarith) hprod
        (by simpa using hc₁)
      exact Or.inl rfl
    · obtain ⟨rfl, rfl, rfl⟩ := five_signed_degree_case_b hf₂ hf₃ (by linarith) hprod
        (by simpa using hc₂)
      exact Or.inr (Or.inl rfl)
  · intro δ₁ δ₂ δ₃ f₁ f₂ f₃ hrow
    rcases hrow with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ := h <;> decide

end CFSG.Semidihedral.Principal
