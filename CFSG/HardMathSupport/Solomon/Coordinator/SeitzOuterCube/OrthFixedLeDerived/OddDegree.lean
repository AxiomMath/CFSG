module

public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube

theorem isSquare_of_isSquare_algebraMap_of_odd_finrank {k K : Type*} [Field k] [Field K]
    [Algebra k K] (hodd : Odd (Module.finrank k K)) {a : k} (ha : IsSquare (algebraMap k K a)) :
    IsSquare a := by
  by_cases h0 : a = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨b, hb⟩ := ha
  obtain ⟨m, hm⟩ := hodd
  have hfd : FiniteDimensional k K := Module.finite_of_finrank_pos (by omega)
  have h1 : a ^ Module.finrank k K = Algebra.norm k b * Algebra.norm k b := by
    rw [← Algebra.norm_algebraMap (R := k) (S := K) a, hb, map_mul]
  refine ⟨Algebra.norm k b / a ^ m, ?_⟩
  rw [hm] at h1
  have ham : a ^ m ≠ 0 := pow_ne_zero m h0
  field_simp
  linear_combination h1

theorem squareClassMap_injective_of_odd_finrank {k K : Type*} [Field k] [Field K] [Algebra k K]
    (hodd : Odd (Module.finrank k K)) :
    Function.Injective (algebraMap k K).squareClassMap := by
  rw [← LinearMap.ker_eq_bot (R := ZMod 2), LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨u, rfl⟩ : ∃ u : kˣ, TauCeti.squareClass u = x :=
    ⟨Additive.toMul (Quotient.out x), TauCeti.squareClass_toMul_out x⟩
  rw [RingHom.squareClassMap_apply, TauCeti.squareClass_eq_zero_iff] at hx
  rw [TauCeti.squareClass_eq_zero_iff]
  have hx' : IsSquare (algebraMap k K (u : k)) := by
    obtain ⟨r, hr⟩ := hx
    exact ⟨(r : K), by simpa using congrArg Units.val hr⟩
  obtain ⟨r, hr⟩ := isSquare_of_isSquare_algebraMap_of_odd_finrank hodd hx'
  have hr0 : r ≠ 0 := fun h => u.ne_zero (by rw [hr, h, mul_zero])
  exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
