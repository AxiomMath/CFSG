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

namespace CFSG.LargeExtraspecial.S14

open Module

section Flag

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

theorem finrank_map_add_finrank_inf_ker_of (f : E →ₗ[ZMod 2] F) (U : Submodule (ZMod 2) E) :
    finrank (ZMod 2) (U.map f) + finrank (ZMod 2) ↥(U ⊓ LinearMap.ker f) =
      finrank (ZMod 2) U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  rw [← h1, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem finrank_map_add_finrank_map_mkQ_le (φ : E →ₗ[ZMod 2] E) {A B : Submodule (ZMod 2) E}
    (hAB : A ≤ B) (hA : A.map φ ≤ A) :
    finrank (ZMod 2) (A.map φ) + finrank (ZMod 2) ((B.map φ).map A.mkQ) ≤
      finrank (ZMod 2) (B.map φ) := by
  have h := finrank_map_add_finrank_inf_ker_of A.mkQ (B.map φ)
  rw [Submodule.ker_mkQ] at h
  have := Submodule.finrank_mono (le_inf (Submodule.map_mono hAB) hA)
  omega

end Flag

end CFSG.LargeExtraspecial.S14
