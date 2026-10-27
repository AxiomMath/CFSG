module

public import CFSG.YGroups.Y443.Native.Words
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

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] def fW1 : List Native.Gen :=
  [.rho (true, 531, 3205), .rho (false, 0, 663), .rho (false, 0, 46),
    .perm #[5, 1, 3, 2, 0, 6, 4, 7, 9, 22, 19, 12, 11, 20, 17, 14, 8, 23, 18, 13, 10, 21, 16, 15],
    .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 20, 17, 18, 19, 16, 21, 23, 22],
    .tau, .tau, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 16, 1, 6, 11, 19, 2, 7, 9, 17, 3, 5, 10, 18, 12, 23, 21, 22, 20, 15, 14, 13],
    .tau, .tau, .xi, .rho (false, 0, 58),
    .perm #[1, 4, 2, 3, 0, 5, 6, 7, 8, 12, 20, 16, 13, 9, 17, 21, 19, 23, 15, 11, 22, 18, 10, 14]]

@[expose] def fW2 : List Native.Gen :=
  [.rho (true, 1694, 2529), .rho (false, 0, 663), .rho (false, 0, 36),
    .perm #[6, 2, 0, 1, 10, 19, 15, 22, 3, 4, 5, 7, 9, 16, 12, 21, 11, 23, 18, 14, 8, 13, 20, 17],
    .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 20, 17, 18, 19, 16, 21, 23, 22],
    .tau, .tau, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 20, 1, 7, 10, 22, 2, 5, 11, 23, 3, 6, 9, 21, 16, 14, 15, 13, 12, 18, 17, 19],
    .tau, .tau, .xi, .rho (false, 0, 58),
    .perm #[1, 8, 2, 3, 0, 9, 10, 11, 4, 12, 16, 20, 13, 5, 23, 18, 22, 17, 15, 7, 19, 21, 6, 14]]

@[expose] def e3W : List Native.Gen :=
  [.rho (false, 0, 1952)]

@[expose] def fW3 : List Native.Gen :=
  [.rho (true, 2085, 899), .rho (false, 0, 2215), .rho (false, 0, 30),
    .perm #[5, 1, 3, 2, 9, 22, 19, 12, 0, 6, 4, 7, 11, 20, 17, 14, 10, 15, 21, 16, 8, 18, 13, 23],
    .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 20, 17, 18, 19, 16, 21, 23, 22],
    .tau, .tau, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 16, 1, 6, 11, 19, 2, 7, 9, 17, 3, 5, 10, 18, 12, 23, 21, 22, 20, 15, 14, 13],
    .tau, .tau, .xi, .rho (false, 0, 58),
    .perm #[1, 8, 2, 3, 0, 9, 10, 11, 4, 12, 16, 20, 13, 5, 23, 18, 22, 17, 15, 7, 19, 21, 6, 14]]

@[expose] def nodeW : ℕ → List Native.Gen
  | 0 => L 0
  | 1 => L 1
  | 2 => L 2
  | 3 => L 3
  | 4 => fW1
  | 5 => L 4
  | 6 => L 5
  | 7 => L 6
  | 8 => L 7
  | 9 => fW2
  | 10 => L 8
  | 11 => L 9
  | 12 => L 10
  | 13 => e3W
  | 14 => fW3
  | _ => []

end CFSG.AGLEmbedding.Norton.MON5_7
