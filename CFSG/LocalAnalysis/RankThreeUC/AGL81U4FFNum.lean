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

namespace CFSG.LocalAnalysis.RankThreeUC

theorem two_factor_numerics {a s₁ s₂ g₁ g₂ ε₁ ε₂ : ℕ} (ha : 0 < a) (hε₁ : ε₁ = 1 ∨ ε₁ = 2)
    (hε₂ : ε₂ = 1 ∨ ε₂ = 2) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hB₁ : a * g₁ ≤ ε₁ * s₁)
    (hB₂ : a * g₂ ≤ ε₂ * s₂) (hC₁ : 2 * g₁ ≤ s₁) (hC₂ : 2 * g₂ ≤ s₂)
    (hchain : s₁ * s₂ ≤ a * (g₁ * g₂)) :
    a = 4 ∧ ε₁ = 2 ∧ ε₂ = 2 ∧ s₁ = 2 * g₁ ∧ s₂ = 2 * g₂ := by
  have hg : 0 < g₁ * g₂ := Nat.mul_pos hg₁ hg₂
  have h4 : 4 * (g₁ * g₂) ≤ s₁ * s₂ := by nlinarith
  have ha4 : 4 ≤ a := by
    by_contra h
    push Not at h
    have : a * (g₁ * g₂) < 4 * (g₁ * g₂) := Nat.mul_lt_mul_of_pos_right h hg
    omega
  have hprod : a * a * (g₁ * g₂) ≤ ε₁ * ε₂ * (a * (g₁ * g₂)) := by
    calc a * a * (g₁ * g₂) = (a * g₁) * (a * g₂) := by ring
      _ ≤ (ε₁ * s₁) * (ε₂ * s₂) := Nat.mul_le_mul hB₁ hB₂
      _ = ε₁ * ε₂ * (s₁ * s₂) := by ring
      _ ≤ ε₁ * ε₂ * (a * (g₁ * g₂)) := Nat.mul_le_mul_left _ hchain
  have haε : a ≤ ε₁ * ε₂ := by
    have h1 : a * (a * (g₁ * g₂)) ≤ (ε₁ * ε₂) * (a * (g₁ * g₂)) := by
      calc a * (a * (g₁ * g₂)) = a * a * (g₁ * g₂) := by ring
        _ ≤ _ := hprod
    exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos ha hg)
  have hε1 : ε₁ = 2 := by
    rcases hε₁ with h | h
    · rcases hε₂ with h' | h' <;> subst h <;> subst_vars <;> omega
    · exact h
  have hε2 : ε₂ = 2 := by
    rcases hε₂ with h | h
    · rcases hε₁ with h' | h' <;> subst h <;> omega
    · exact h
  subst hε1 hε2
  have ha4' : a = 4 := by omega
  subst ha4'
  have hs12 : s₁ * s₂ = 4 * (g₁ * g₂) := by omega
  have hs1 : s₁ = 2 * g₁ := by
    by_contra h
    have h' : 2 * g₁ < s₁ := lt_of_le_of_ne hC₁ (Ne.symm h)
    have : 2 * g₁ * (2 * g₂) < s₁ * s₂ := Nat.mul_lt_mul_of_lt_of_le h' hC₂ (by omega)
    nlinarith
  have hs2 : s₂ = 2 * g₂ := by
    by_contra h
    have h' : 2 * g₂ < s₂ := lt_of_le_of_ne hC₂ (Ne.symm h)
    have : 2 * g₁ * (2 * g₂) < s₁ * s₂ := Nat.mul_lt_mul_of_le_of_lt hC₁ h' (by omega)
    nlinarith
  exact ⟨rfl, rfl, rfl, hs1, hs2⟩

end CFSG.LocalAnalysis.RankThreeUC
