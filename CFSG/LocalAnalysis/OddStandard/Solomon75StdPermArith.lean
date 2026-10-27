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

namespace CFSG.OddStandard.Solomon75

theorem pair_arith {n m f m' f' : ℕ} (hn : 8 ≤ n) (h : n = 2 * m + f) (h' : n = 2 * m' + f')
    (hm : Even m) (hm2 : 2 ≤ m) (hm' : Even m') (hm2' : 2 ≤ m')
    (h1 : 5 ≤ f → 2 * f ≤ m') (h1' : 5 ≤ f' → 2 * f' ≤ m)
    (h2 : f = 4 → 6 ≤ m') (h2' : f' = 4 → 6 ≤ m)
    (h3 : 7 ≤ m → m - 2 ≤ max (m' / 2) f') (h3' : 7 ≤ m' → m' - 2 ≤ max (m / 2) f) :
    (m = 4 ∨ m = 6) ∧ (m' = 4 ∨ m' = 6) ∧ n ≤ 16 ∧ (12 ≤ n → m = 6 ∨ m' = 6) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hm'
  omega

end CFSG.OddStandard.Solomon75
