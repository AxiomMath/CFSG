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

@[expose] def tW : List Native.Gen :=
  [.rho (true, 0, 0)]

@[expose] def dW : List Native.Gen :=
  [.rho (false, 0, 2708), .rho (false, 0, 30),
  .perm #[10, 5, 12, 18, 15, 7, 16, 11, 8, 13, 17, 6, 0, 2, 1, 20, 14, 9, 4, 19, 23, 21, 3, 22]]

@[expose] def zW : List Native.Gen :=
  [.tau, .tau, .rho (false, 3916, 844), .tau, .rho (true, 2260, 1542), .rho (false, 0, 4075),
  .rho (false, 0, 24),
  .perm #[17, 22, 1, 0, 18, 15, 14, 20, 13, 5, 3, 10, 7, 23, 6, 16, 9, 19, 8, 21, 2, 4, 12, 11],
  .xi, .xi, .rho (false, 0, 8),
  .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
  .xi, .rho (false, 0, 4),
  .perm #[0, 2, 8, 21, 9, 23, 13, 14, 4, 18, 1, 15, 12, 3, 5, 17, 11, 22, 7, 6, 19, 16, 20, 10],
  .tau, .xi, .xi, .rho (false, 0, 8),
  .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
  .xi, .rho (false, 0, 38),
  .perm #[4, 6, 9, 17, 11, 16, 22, 21, 5, 20, 12, 2, 15, 3, 23, 7, 14, 13, 8, 19, 18, 10, 0, 1],
  .tau, .tau, .xi, .rho (false, 0, 36),
  .perm #[0, 5, 14, 15, 1, 4, 10, 11, 2, 6, 21, 20, 7, 3, 17, 16, 18, 23, 8, 12, 19, 22, 13, 9],
  .xi, .rho (false, 0, 6),
  .perm #[0, 2, 9, 12, 10, 17, 19, 13, 1, 21, 16, 6, 7, 14, 5, 11, 15, 20, 8, 22, 4, 3, 23, 18],
  .tau, .tau, .xi, .rho (false, 0, 2),
  .perm #[0, 4, 8, 9, 1, 5, 13, 12, 2, 7, 17, 16, 6, 3, 20, 21, 23, 19, 15, 10, 22, 18, 11, 14],
  .xi, .xi, .rho (false, 0, 0),
  .perm #[0, 1, 2, 16, 7, 11, 20, 15, 14, 22, 8, 5, 3, 19, 18, 17, 23, 4, 10, 13, 9, 21, 6, 12],
  .tau, .xi, .rho (false, 0, 24),
  .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
  .xi, .rho (false, 0, 60),
  .perm #[8, 9, 12, 21, 13, 16, 17, 20, 2, 19, 4, 11, 15, 1, 23, 3, 5, 14, 6, 22, 18, 7, 10, 0],
  .tau, .tau, .xi, .xi, .rho (false, 0, 2),
  .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
  .xi, .rho (false, 0, 0),
  .perm #[2, 3, 5, 12, 7, 23, 15, 20, 8, 21, 0, 17, 10, 4, 13, 11, 1, 9, 19, 22, 14, 16, 18, 6],
  .tau, .xi, .xi, .rho (false, 0, 24),
  .perm #[0, 6, 10, 11, 1, 7, 13, 12, 2, 5, 16, 17, 4, 3, 23, 22, 20, 18, 15, 8, 21, 19, 9, 14],
  .xi, .xi, .rho (false, 0, 32),
  .perm #[4, 6, 8, 13, 9, 17, 19, 14, 16, 21, 5, 2, 22, 11, 20, 12, 10, 1, 15, 3, 0, 18, 23, 7]]

@[expose] def eW : List Native.Gen :=
  [.tau, .tau, .rho (false, 1065, 835), .tau, .rho (false, 3748, 868), .rho (false, 0, 2656),
  .rho (false, 0, 34),
  .perm #[3, 19, 0, 1, 6, 23, 9, 13, 22, 7, 14, 11, 2, 18, 17, 16, 15, 20, 5, 8, 10, 21, 12, 4],
  .xi, .xi, .rho (false, 0, 24),
  .perm #[0, 6, 10, 11, 1, 7, 13, 12, 2, 5, 16, 17, 4, 3, 23, 22, 20, 18, 15, 8, 21, 19, 9, 14],
  .xi, .xi, .rho (false, 0, 12),
  .perm #[0, 2, 4, 7, 12, 20, 21, 13, 8, 9, 16, 17, 22, 15, 23, 14, 5, 1, 6, 3, 18, 10, 11, 19],
  .tau, .tau, .xi, .rho (false, 0, 24),
  .perm #[0, 6, 22, 23, 1, 7, 17, 16, 2, 5, 12, 13, 4, 3, 11, 10, 8, 14, 19, 20, 9, 15, 21, 18],
  .xi, .rho (false, 0, 56),
  .perm #[3, 7, 9, 12, 10, 23, 19, 11, 14, 22, 15, 18, 17, 20, 1, 0, 16, 5, 4, 21, 6, 13, 2, 8],
  .xi, .xi, .tau, .xi, .xi, .rho (false, 0, 14),
  .perm #[0, 5, 12, 13, 1, 4, 8, 9, 2, 6, 23, 22, 7, 3, 19, 18, 16, 21, 10, 14, 17, 20, 15, 11],
  .xi, .rho (false, 0, 4),
  .perm #[1, 4, 8, 10, 11, 12, 18, 23, 9, 14, 21, 16, 6, 3, 13, 15, 5, 19, 17, 2, 7, 20, 0, 22],
  .xi, .xi, .tau, .xi, .xi, .rho (false, 0, 2),
  .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
  .xi, .rho (false, 0, 42),
  .perm #[4, 6, 8, 13, 11, 20, 22, 12, 1, 10, 3, 15, 21, 2, 5, 16, 18, 23, 0, 7, 9, 19, 14, 17],
  .tau, .tau, .xi, .xi, .rho (false, 0, 18),
  .perm #[0, 7, 10, 11, 1, 6, 12, 13, 2, 4, 18, 19, 5, 3, 20, 21, 23, 16, 14, 8, 22, 17, 9, 15],
  .xi, .xi, .rho (false, 0, 62),
  .perm #[9, 10, 13, 17, 14, 22, 21, 18, 1, 23, 7, 8, 12, 0, 19, 2, 4, 15, 5, 16, 20, 6, 11, 3],
  .tau, .xi, .rho (false, 0, 0),
  .perm #[0, 1, 3, 4, 2, 5, 6, 7, 8, 14, 23, 17, 16, 22, 15, 9, 20, 18, 11, 13, 12, 10, 19, 21],
  .xi, .xi, .rho (false, 0, 46),
  .perm #[6, 7, 8, 10, 13, 14, 20, 21, 0, 19, 17, 3, 2, 16, 1, 18, 15, 12, 23, 22, 5, 4, 9, 11],
  .tau, .xi, .rho (false, 0, 12),
  .perm #[7, 19, 2, 3, 0, 9, 15, 21, 1, 10, 20, 13, 16, 5, 11, 8, 17, 14, 12, 4, 18, 23, 6, 22],
  .xi, .rho (false, 0, 44),
  .perm #[15, 9, 2, 3, 4, 5, 8, 14, 0, 7, 21, 19, 18, 20, 1, 6, 23, 22, 13, 10, 12, 11, 17, 16]]

@[expose] def sevenOrderPairs : List (List Native.Gen × List Native.Gen) :=
  [(powL 7 dW, []), (powL 7 zW, []), (powL 7 eW, [])]

@[expose] def sevenCommPairs : List (List Native.Gen × List Native.Gen) :=
  [(dW ++ zW, zW ++ dW), (dW ++ eW, eW ++ dW), (zW ++ eW, eW ++ zW)]

@[expose] def sevenActPairs : List (List Native.Gen × List Native.Gen) :=
  [(tW ++ tW, []), (tW ++ dW, dW ++ tW), (tW ++ zW ++ tW ++ zW, []), (tW ++ eW ++ tW ++ eW, [])]

@[expose] def sevenNeWord (k : ℕ) : List Native.Gen := powL ((7 - k) % 7) zW ++ eW

end CFSG.AGLEmbedding.Norton.MON5_7
