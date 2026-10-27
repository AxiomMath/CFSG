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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.G23F48

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

theorem eq_smul_one_of_frame {g V W : Matrix n n K} (hWV : W * V = 1) {c u : n → K}
    (hc : ∀ i, c i ≠ 0) (hWu : W *ᵥ u = c) {lam : n → K}
    (hcol : ∀ i, g *ᵥ (fun j => V j i) = lam i • fun j => V j i) {μ : K}
    (hu : g *ᵥ u = μ • u) : g = μ • 1 := by
  have hVW : V * W = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl n)).1 hWV
  have key : ∀ x : n → K, W *ᵥ (V *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hWV, Matrix.one_mulVec]
  have hgV : g * V = V * Matrix.diagonal lam := by
    ext j i
    have := congrFun (hcol i) j
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, this, Matrix.mul_diagonal, mul_comm]
  have huc : u = V *ᵥ c := by
    rw [← hWu, Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]
  have h2 : Matrix.diagonal lam *ᵥ c = μ • c := by
    have e : V *ᵥ (Matrix.diagonal lam *ᵥ c) = V *ᵥ (μ • c) := by
      rw [Matrix.mulVec_mulVec, ← hgV, ← Matrix.mulVec_mulVec, ← huc, hu, Matrix.mulVec_smul,
        ← huc]
    have := congrArg (W *ᵥ ·) e
    rwa [key, key] at this
  have hlam : ∀ i, lam i = μ := fun i => by
    have := congrFun h2 i
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ (hc i) this
  have hd : Matrix.diagonal lam = μ • (1 : Matrix n n K) := by
    have hl : lam = fun _ => μ := funext hlam
    rw [hl]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  calc g = g * (V * W) := by rw [hVW, Matrix.mul_one]
    _ = V * Matrix.diagonal lam * W := by rw [← Matrix.mul_assoc, hgV]
    _ = μ • 1 := by rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVW]

end CFSG.KC.G23F48
