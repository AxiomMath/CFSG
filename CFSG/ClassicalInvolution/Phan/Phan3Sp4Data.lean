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

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable

@[expose] def sp4Codes : List (List Nat) :=
  [[4, 4, 4], [2, 2, 2], [6, 6, 6], [0, 0, 0], [4, 3, 5, 2], [6, 1, 7, 0], [5, 7, 4, 7, 5, 6],
   [1, 3, 0, 3, 1, 2], [4, 0, 5, 1, 4, 1, 5, 0], [4, 6, 3, 7, 5, 7, 2, 6],
   [6, 2, 7, 3, 6, 3, 7, 2], [7, 3, 1, 3, 7, 2, 0, 2], [5, 1, 3, 1, 5, 0, 2, 0],
   [4, 7, 3, 6, 3, 5, 7, 3, 7, 3, 7]]

@[expose] def sp4Rels : List (List (Fin 4 × Bool)) := sp4Codes.map (decodeWord 4)

end CFSG.ClassicalInvolution.Phan.Q3G
