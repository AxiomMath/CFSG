module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33

open Matrix

variable {F : Type} [Field F]

theorem eq_smul_cross_of_dot_eq_zero (u w v : Fin 3 → F) (hn : u ⨯₃ w ≠ 0)
    (hu : v ⬝ᵥ u = 0) (hw : v ⬝ᵥ w = 0) : ∃ t : F, v = t • (u ⨯₃ w) := by
  have h1 : (u ⨯₃ w) ⨯₃ v = 0 := by
    rw [cross_cross_eq_smul_sub_smul, dotProduct_comm u v, dotProduct_comm w v, hu, hw]
    simp
  have hli : ¬ LinearIndependent F ![u ⨯₃ w, v] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    exact not_not.mpr h1
  rw [LinearIndependent.pair_iff' hn] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, ha.symm⟩

theorem no_two_isotropic (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x) (u w : Fin 3 → F)
    (huu : (σ ∘ u) ⬝ᵥ u = 0) (huw : (σ ∘ u) ⬝ᵥ w = 0) (hww : (σ ∘ w) ⬝ᵥ w = 0)
    (hli : LinearIndependent F ![u, w]) : False := by
  have hwu : (σ ∘ w) ⬝ᵥ u = 0 := by
    have := congrArg σ huw
    simp only [dotProduct, map_sum, map_mul, Function.comp_apply, hσσ, map_zero] at this
    simpa [dotProduct, mul_comm] using this
  have hn : u ⨯₃ w ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hli
  obtain ⟨s, hs⟩ := eq_smul_cross_of_dot_eq_zero u w (σ ∘ u) hn huu huw
  obtain ⟨t, ht⟩ := eq_smul_cross_of_dot_eq_zero u w (σ ∘ w) hn hwu hww
  have hu0 : u ≠ 0 := hli.ne_zero 0
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hu0
    funext j
    have := congrFun hs j
    simp only [Function.comp_apply, zero_smul, Pi.zero_apply] at this
    have h2 := congrArg σ this
    simpa [hσσ] using h2
  have hw' : w = σ (t / s) • u := by
    funext j
    have h1 := congrFun hs j
    have h2 := congrFun ht j
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have h3 : σ (w j) = (t / s) * σ (u j) := by
      rw [h2, h1]
      field_simp
    have h4 := congrArg σ h3
    rw [hσσ, map_mul, hσσ] at h4
    exact h4
  rw [LinearIndependent.pair_iff' hu0] at hli
  exact hli (σ (t / s)) hw'.symm

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33
