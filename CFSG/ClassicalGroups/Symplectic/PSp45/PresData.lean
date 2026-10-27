module

public import CFSG.ClassicalInvolution.Phan.Phan3AData
public import Certificates.Data.CFSGNative.CosetTable.Enum
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

namespace CFSG.ClassicalGroups.Symplectic.PSp45

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G

@[expose] def pspCodes : List (List Nat) :=
  [[0, 0, 0, 0, 0], [2, 2, 2, 2, 2], [6, 6, 6, 6, 6], [1, 3, 0, 2], [1, 5, 0, 4], [1, 7, 0, 6],
   [3, 5, 2, 4], [7, 2, 6, 5, 3, 0], [7, 4, 6, 5, 0, 0], [9, 11, 8, 10], [8, 8, 11, 11],
   [8, 8, 8, 8], [9, 2, 8, 3], [11, 2, 10, 3, 3, 3, 3], [9, 6, 8, 7, 7], [11, 6, 10, 7, 7, 7],
   [12, 12], [13, 0, 12, 3], [13, 8, 12, 11], [15, 4, 14, 7], [14, 2, 14, 2, 14, 2],
   [10, 10, 12, 8, 10, 6, 10, 10, 12, 8, 10, 6, 10, 10, 12, 8, 10, 6],
   [12, 14, 12, 14, 12, 14, 12, 14], [10, 14, 3, 3, 3, 15, 3, 3, 14, 3, 3, 3]]

@[expose] def pspRels : List (List (Fin 8 × Bool)) := pspCodes.map (decodeWord 8)

end CFSG.ClassicalGroups.Symplectic.PSp45
