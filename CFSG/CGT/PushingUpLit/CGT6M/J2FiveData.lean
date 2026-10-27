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

namespace CFSG.CGT.PushingUpLit.CGT6M

@[expose] def wordX : List (ℕ × Bool) :=
  [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
   (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
   (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true)]

@[expose] def wordG : List (ℕ × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
   (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
   (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true),
   (1, true), (1, true)]

@[expose] def matX : List (List ℕ) :=
  [[0, 4, 2, 1, 0, 1, 3, 2, 0, 2, 3, 1, 3, 3],
   [3, 4, 2, 3, 2, 0, 1, 2, 4, 0, 2, 3, 0, 4],
   [2, 3, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4, 4],
   [2, 4, 4, 1, 4, 0, 0, 1, 0, 1, 1, 1, 1, 3],
   [3, 2, 2, 4, 1, 0, 1, 1, 4, 1, 2, 4, 3, 4],
   [1, 3, 0, 3, 2, 0, 4, 1, 2, 4, 1, 4, 0, 2],
   [3, 0, 2, 0, 0, 3, 3, 4, 1, 0, 2, 2, 1, 2],
   [4, 1, 0, 3, 4, 1, 4, 1, 0, 3, 2, 0, 4, 1],
   [2, 4, 2, 4, 2, 0, 0, 3, 4, 2, 1, 3, 0, 1],
   [4, 4, 0, 4, 2, 4, 3, 1, 1, 3, 0, 4, 4, 2],
   [0, 4, 0, 1, 0, 2, 4, 1, 4, 2, 1, 4, 0, 1],
   [3, 1, 4, 3, 2, 3, 4, 1, 1, 2, 1, 2, 0, 3],
   [4, 0, 0, 3, 4, 1, 1, 1, 0, 1, 2, 4, 2, 1],
   [2, 1, 4, 3, 3, 0, 0, 4, 1, 4, 4, 1, 0, 1]]

@[expose] def matG : List (List ℕ) :=
  [[3, 3, 4, 1, 3, 2, 2, 3, 1, 0, 1, 3, 4, 0],
   [2, 3, 4, 0, 3, 4, 0, 0, 4, 3, 2, 0, 4, 0],
   [1, 1, 2, 2, 2, 1, 0, 1, 2, 3, 0, 2, 2, 1],
   [0, 3, 2, 0, 2, 3, 3, 2, 3, 4, 3, 2, 3, 2],
   [2, 0, 4, 4, 4, 4, 1, 0, 4, 4, 2, 0, 2, 3],
   [1, 1, 2, 2, 4, 1, 1, 4, 3, 3, 0, 0, 3, 4],
   [1, 3, 4, 1, 3, 2, 0, 2, 2, 3, 1, 4, 0, 1],
   [2, 1, 0, 4, 1, 1, 1, 0, 4, 2, 1, 0, 1, 4],
   [0, 2, 3, 0, 3, 2, 2, 2, 2, 0, 1, 4, 3, 0],
   [4, 1, 2, 1, 2, 2, 0, 4, 3, 4, 0, 0, 3, 2],
   [4, 0, 1, 2, 1, 2, 4, 3, 4, 3, 3, 3, 0, 2],
   [1, 2, 4, 0, 0, 2, 4, 3, 2, 1, 1, 0, 0, 0],
   [0, 1, 4, 4, 2, 1, 1, 4, 0, 2, 2, 4, 4, 2],
   [0, 1, 1, 2, 1, 2, 4, 4, 2, 0, 1, 1, 2, 3]]

end CFSG.CGT.PushingUpLit.CGT6M
