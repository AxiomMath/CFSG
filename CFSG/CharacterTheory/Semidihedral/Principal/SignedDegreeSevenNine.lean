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

theorem signed_degree_pattern_a_lt {Q f₁ f₂ f₃ : ℤ} (hf₁ : 1 < f₁) (hf₃ : 1 < f₃)
    (hsum : 1 - f₁ + f₂ - f₃ = 0) (hprod : f₁ * f₂ = Q * f₃) :
    f₂ = f₁ + f₃ - 1 ∧ f₁ < Q ∧ f₁ * (f₁ - 1) = f₃ * (Q - f₁) := by
  have hf₂ : f₂ = f₁ + f₃ - 1 := by linarith
  subst hf₂
  have heq : f₁ * (f₁ - 1) = f₃ * (Q - f₁) := by linarith
  refine ⟨rfl, ?_, heq⟩
  nlinarith

theorem signed_degree_pattern_b_lt {Q f₁ f₂ f₃ : ℤ} (hf₂ : 1 < f₂) (hf₃ : 1 < f₃)
    (hsum : 1 + f₁ - f₂ - f₃ = 0) (hprod : f₁ * f₂ = Q * f₃) :
    f₁ = f₂ + f₃ - 1 ∧ f₂ < Q ∧ f₂ * (f₂ - 1) = f₃ * (Q - f₂) := by
  have hf₁ : f₁ = f₂ + f₃ - 1 := by linarith
  subst hf₁
  have heq : f₂ * (f₂ - 1) = f₃ * (Q - f₂) := by linarith
  refine ⟨rfl, ?_, heq⟩
  nlinarith

theorem signed_degree_pattern_c_bounds {Q f₁ f₂ f₃ : ℤ} (hQ : 2 ≤ Q) (hf₁ : 1 < f₁)
    (hf₂ : 1 < f₂) (hsum : 1 - f₁ - f₂ + f₃ = 0) (hprod : f₁ * f₂ = Q * f₃) :
    f₃ = f₁ + f₂ - 1 ∧ (f₁ - Q) * (f₂ - Q) = Q * (Q - 1) ∧ Q < f₁ ∧ Q < f₂ ∧ f₁ ≤ Q * Q := by
  have hf₃ : f₃ = f₁ + f₂ - 1 := by linarith
  subst hf₃
  have hfac : (f₁ - Q) * (f₂ - Q) = Q * (Q - 1) := by linarith
  have hpos : 0 < Q * (Q - 1) := by nlinarith
  have hpos₁ : Q < f₁ := by
    by_contra hle
    push Not at hle
    have hlt₁ : f₁ < Q := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · rw [h, sub_self, zero_mul] at hfac; linarith
    have hlt₂ : f₂ < Q := by
      by_contra hge
      push Not at hge
      nlinarith
    nlinarith
  have hpos₂ : Q < f₂ := by nlinarith
  refine ⟨rfl, hfac, hpos₁, hpos₂, ?_⟩
  nlinarith

theorem seven_signed_degree_cases (f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ) (hf₁ : 1 < f₁) (hf₂ : 1 < f₂)
    (hf₃ : 1 < f₃)
    (hsigns : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hsum : 1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0) (hprod : f₁ * f₂ = 49 * f₃)
    (hc₁ : f₁ ≡ δ₁ * 9 [ZMOD 32]) (hc₂ : f₂ ≡ 7 * δ₂ [ZMOD 32]) :
    (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∧
      ((f₁ = 55 ∧ f₂ = 441 ∧ f₃ = 495) ∨ (f₁ = 343 ∧ f₂ = 57 ∧ f₃ = 399)) := by
  rw [Int.ModEq] at hc₁ hc₂
  rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, hfac, hlt₁, hlt₂, hle₁⟩ :=
      signed_degree_pattern_c_bounds (Q := 49) (by norm_num) hf₁ hf₂ (by linarith) hprod
    refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, f₁ = 32 * k + 23 := ⟨(f₁ - 23) / 32, by omega⟩
    have hk : k ≤ 74 := by omega
    have hk0 : 0 ≤ k := by omega
    interval_cases k <;> omega
  · exfalso
    obtain ⟨-, hlt, heq⟩ := signed_degree_pattern_a_lt (Q := 49) hf₁ hf₃ (by linarith) hprod
    interval_cases f₁ <;> omega
  · exfalso
    obtain ⟨rfl, hlt, heq⟩ := signed_degree_pattern_b_lt (Q := 49) hf₂ hf₃ (by linarith) hprod
    interval_cases f₂ <;> omega

theorem nine_signed_degree_cases (f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ) (hf₁ : 1 < f₁) (hf₂ : 1 < f₂)
    (hf₃ : 1 < f₃)
    (hsigns : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hsum : 1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0) (hprod : f₁ * f₂ = 81 * f₃)
    (hc₁ : f₁ ≡ δ₁ * (-7) [ZMOD 32]) (hc₂ : f₂ ≡ -9 * δ₂ [ZMOD 32]) :
    ((δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1) ∧ f₁ = 729 ∧ f₂ = 73 ∧ f₃ = 657) ∨
      ((δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∧ f₁ = 71 ∧ f₂ = 567 ∧ f₃ = 497) ∨
      ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∧ f₁ = 135 ∧ f₂ = 201 ∧ f₃ = 335) := by
  rw [Int.ModEq] at hc₁ hc₂
  rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, hfac, hlt₁, hlt₂, hle₁⟩ :=
      signed_degree_pattern_c_bounds (Q := 81) (by norm_num) hf₁ hf₂ (by linarith) hprod
    refine Or.inr (Or.inr ⟨⟨rfl, rfl, rfl⟩, ?_⟩)
    obtain ⟨k, rfl⟩ : ∃ k, f₁ = 32 * k + 7 := ⟨(f₁ - 7) / 32, by omega⟩
    have hk : k ≤ 205 := by omega
    have hk0 : 0 ≤ k := by omega
    interval_cases k <;> omega
  · obtain ⟨rfl, hlt, heq⟩ := signed_degree_pattern_a_lt (Q := 81) hf₁ hf₃ (by linarith) hprod
    refine Or.inr (Or.inl ⟨⟨rfl, rfl, rfl⟩, ?_⟩)
    interval_cases f₁ <;> omega
  · obtain ⟨rfl, hlt, heq⟩ := signed_degree_pattern_b_lt (Q := 81) hf₂ hf₃ (by linarith) hprod
    refine Or.inl ⟨⟨rfl, rfl, rfl⟩, ?_⟩
    interval_cases f₂ <;> omega

theorem seven_nine_signed_degree_product_finite_alternatives :
    (∀ q e f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ, (q = 7 ∧ e = -1 ∨ q = 9 ∧ e = 1) →
      1 < f₁ → 1 < f₂ → 1 < f₃ → Odd f₁ → Odd f₂ → Odd f₃ →
      ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
        (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) →
      1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0 → f₁ * f₂ = q ^ 2 * f₃ →
      f₁ ≡ δ₁ * (2 - e * q) [ZMOD 32] → f₂ ≡ -δ₂ * e * q [ZMOD 32] →
      (q = 7 ∧ (δ₁, δ₂, δ₃) = (-1, -1, 1) ∧
          ((f₁, f₂, f₃) = (55, 441, 495) ∨ (f₁, f₂, f₃) = (343, 57, 399))) ∨
        (q = 9 ∧ (((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((1, -1, -1), (729, 73, 657)) ∨
          ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, 1, -1), (71, 567, 497)) ∨
          ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, -1, 1), (135, 201, 335))))) ∧
    (∀ q e f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ,
      ((q = 7 ∧ e = -1 ∧ (δ₁, δ₂, δ₃) = (-1, -1, 1) ∧
          ((f₁, f₂, f₃) = (55, 441, 495) ∨ (f₁, f₂, f₃) = (343, 57, 399))) ∨
        (q = 9 ∧ e = 1 ∧ (((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((1, -1, -1), (729, 73, 657)) ∨
          ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, 1, -1), (71, 567, 497)) ∨
          ((δ₁, δ₂, δ₃), (f₁, f₂, f₃)) = ((-1, -1, 1), (135, 201, 335))))) →
      1 < f₁ ∧ 1 < f₂ ∧ 1 < f₃ ∧ Odd f₁ ∧ Odd f₂ ∧ Odd f₃ ∧
      ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
        (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
      1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0 ∧ f₁ * f₂ = q ^ 2 * f₃ ∧
      f₁ ≡ δ₁ * (2 - e * q) [ZMOD 32] ∧ f₂ ≡ -δ₂ * e * q [ZMOD 32]) := by
  refine ⟨?_, ?_⟩
  · intro q e f₁ f₂ f₃ δ₁ δ₂ δ₃ hq hf₁ hf₂ hf₃ _ _ _ hsigns hsum hprod hc₁ hc₂
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨⟨rfl, rfl, rfl⟩, h | h⟩ := seven_signed_degree_cases f₁ f₂ f₃ δ₁ δ₂ δ₃ hf₁ hf₂ hf₃
        hsigns hsum (by simpa using hprod) (by simpa [mul_comm] using hc₁)
        (by
          have := hc₂
          rcases hsigns with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> subst h2 <;>
            simpa using this)
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, rfl, Or.inl rfl⟩
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, rfl, Or.inr rfl⟩
    · have h := nine_signed_degree_cases f₁ f₂ f₃ δ₁ δ₂ δ₃ hf₁ hf₂ hf₃ hsigns hsum
        (by simpa using hprod) (by
          have := hc₁
          rcases hsigns with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩ <;> subst h1 <;>
            simpa using this)
        (by
          have := hc₂
          rcases hsigns with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> subst h2 <;>
            simpa using this)
      rcases h with ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ |
        ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
      · exact Or.inr ⟨rfl, Or.inl rfl⟩
      · exact Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩
      · exact Or.inr ⟨rfl, Or.inr (Or.inr rfl)⟩
  · intro q e f₁ f₂ f₃ δ₁ δ₂ δ₃ hrow
    rcases hrow with ⟨rfl, rfl, hδ, hf | hf⟩ | ⟨rfl, rfl, h | h | h⟩ <;>
      simp only [Prod.mk.injEq] at * <;>
      first
        | (obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ := h; decide)
        | (obtain ⟨rfl, rfl, rfl⟩ := hδ; obtain ⟨rfl, rfl, rfl⟩ := hf; decide)

end CFSG.Semidihedral.Principal
