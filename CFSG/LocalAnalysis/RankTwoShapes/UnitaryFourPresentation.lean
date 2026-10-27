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
public import Mathlib.GroupTheory.PresentedGroup
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

namespace CFSG.RankTwoShapes

@[expose] def unitaryFourRels : Set (FreeGroup (Fin 4)) :=
  let x := FreeGroup.of (0 : Fin 4)
  let y := FreeGroup.of (1 : Fin 4)
  let g := FreeGroup.of (2 : Fin 4)
  let h := FreeGroup.of (3 : Fin 4)
  {x ^ 4, y ^ 4,
    x⁻¹ * y⁻¹ * x * y,
    g⁻¹ * h⁻¹ * g * h,
    g ^ 2 * (y ^ 2)⁻¹,
    h ^ 2 * (x ^ 2 * y ^ 2)⁻¹,
    x⁻¹ * g⁻¹ * x * g * (x ^ 2)⁻¹,
    y⁻¹ * g⁻¹ * y * g * (x ^ 2 * y ^ 2)⁻¹,
    x⁻¹ * h⁻¹ * x * h * (x ^ 2 * y ^ 2)⁻¹,
    y⁻¹ * h⁻¹ * y * h * (y ^ 2)⁻¹}

abbrev UnitaryFourPresented : Type := PresentedGroup unitaryFourRels

end CFSG.RankTwoShapes
