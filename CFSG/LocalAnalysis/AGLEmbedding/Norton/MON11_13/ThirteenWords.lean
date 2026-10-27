module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster.AxisCount

@[expose] def thirteenX : List Native.Gen :=
  [.tau,
   .tau,
   .rho (false, 3958, 4041),
   .tau,
   .rho (true, 583, 3476),
   .rho (false, 0, 2662),
   .rho (false, 0, 24),
   .perm #[10, 5, 8, 9, 11, 6, 7, 4, 0, 17, 14, 20, 16, 2, 23, 12, 21, 13, 19, 3, 15, 22, 1, 18],
   .xi,
   .rho (false, 0, 18),
   .perm #[0, 3, 4, 6, 1, 2, 7, 5, 8, 9, 20, 21, 10, 11, 22, 23, 13, 12, 17, 16, 15, 14, 19, 18],
   .tau,
   .tau,
   .xi,
   .xi,
   .rho (false, 0, 8),
   .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
   .xi,
   .rho (false, 0, 42),
   .perm #[2, 7, 8, 18, 9, 23, 11, 15, 12, 22, 4, 5, 21, 17, 19, 13, 0, 20, 3, 14, 10, 6, 1, 16],
   .tau,
   .tau,
   .xi,
   .rho (false, 0, 36),
   .perm #[0, 5, 14, 15, 1, 4, 10, 11, 2, 6, 21, 20, 7, 3, 17, 16, 18, 23, 8, 12, 19, 22, 13, 9],
   .xi,
   .rho (false, 0, 30),
   .perm #[0, 1, 2, 13, 3, 15, 12, 14, 10, 23, 16, 4, 7, 18, 22, 9, 19, 5, 11, 21, 20, 8, 6, 17],
   .tau,
   .xi,
   .rho (false, 0, 12),
   .perm #[7, 19, 2, 3, 0, 9, 15, 21, 1, 10, 20, 13, 16, 5, 11, 8, 17, 14, 12, 4, 18, 23, 6, 22],
   .xi,
   .xi,
   .rho (false, 0, 20),
   .perm #[22, 15, 2, 3, 9, 10, 13, 23, 0, 11, 18, 5, 7, 17, 1, 8, 19, 16, 20, 14, 21, 12, 6, 4],
   .tau,
   .tau,
   .xi,
   .xi,
   .rho (false, 0, 0),
   .perm #[0, 1, 2, 4, 3, 5, 7, 6, 8, 15, 18, 21, 20, 19, 14, 9, 16, 23, 10, 13, 12, 11, 22, 17],
   .xi,
   .rho (false, 0, 58),
   .perm #[0, 2, 3, 4, 11, 14, 16, 21, 1, 6, 5, 7, 23, 18, 12, 9, 15, 17, 10, 20, 19, 8, 13, 22],
   .xi,
   .rho (false, 0, 4),
   .perm #[0, 7, 11, 13, 1, 6, 12, 10, 2, 3, 17, 23, 4, 5, 22, 16, 8, 9, 20, 19, 14, 15, 21, 18],
   .tau,
   .tau,
   .xi,
   .rho (false, 0, 12),
   .perm #[6, 22, 2, 3, 0, 9, 17, 14, 1, 11, 13, 16, 20, 5, 8, 10, 23, 18, 19, 7, 21, 15, 4, 12],
   .xi,
   .rho (false, 0, 24),
   .perm #[6, 7, 2, 3, 10, 11, 14, 15, 0, 1, 4, 5, 12, 13, 8, 9, 22, 19, 23, 18, 16, 20, 21, 17]]

@[expose] def thirteenXi : List Native.Gen :=
  [.tau,
   .tau,
   .rho (false, 2379, 3072),
   .tau,
   .rho (false, 1648, 560),
   .rho (false, 0, 951),
   .rho (false, 0, 22),
   .perm #[3, 11, 14, 15, 2, 10, 7, 6, 8, 1, 18, 16, 0, 9, 20, 23, 19, 21, 12, 5, 17, 22, 4, 13],
   .xi,
   .rho (false, 0, 12),
   .perm #[9, 13, 2, 3, 0, 5, 16, 20, 1, 4, 21, 17, 12, 8, 6, 7, 14, 19, 18, 11, 15, 22, 10, 23],
   .tau,
   .tau,
   .xi,
   .rho (false, 0, 24),
   .perm #[0, 6, 22, 23, 1, 7, 17, 16, 2, 5, 12, 13, 4, 3, 11, 10, 8, 14, 19, 20, 9, 15, 21, 18],
   .xi,
   .rho (false, 0, 2),
   .perm #[2, 5, 10, 13, 17, 20, 23, 21, 1, 14, 6, 9, 3, 11, 12, 4, 0, 7, 8, 15, 22, 19, 18, 16],
   .tau,
   .tau,
   .xi,
   .rho (false, 0, 0),
   .perm #[0, 2, 3, 4, 1, 5, 7, 6, 8, 22, 13, 19, 16, 14, 21, 11, 12, 18, 9, 23, 20, 10, 17, 15],
   .xi,
   .xi,
   .rho (false, 0, 40),
   .perm #[10, 11, 14, 15, 18, 19, 22, 23, 0, 4, 5, 1, 7, 2, 6, 3, 21, 20, 17, 16, 13, 12, 9, 8],
   .tau,
   .tau,
   .xi,
   .rho (false, 0, 24),
   .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
   .xi,
   .rho (false, 0, 32),
   .perm #[2, 3, 10, 23, 11, 18, 20, 16, 9, 13, 15, 22, 19, 14, 5, 0, 7, 21, 8, 4, 12, 1, 17, 6],
   .tau,
   .xi,
   .xi,
   .rho (false, 0, 0),
   .perm #[0, 1, 2, 4, 3, 5, 7, 6, 8, 15, 18, 21, 20, 19, 14, 9, 16, 23, 10, 13, 12, 11, 22, 17],
   .xi,
   .rho (false, 0, 58),
   .perm #[0, 2, 3, 4, 11, 14, 16, 21, 1, 6, 5, 7, 23, 18, 12, 9, 15, 17, 10, 20, 19, 8, 13, 22],
   .xi,
   .rho (false, 0, 4),
   .perm #[0, 7, 11, 13, 1, 6, 12, 10, 2, 3, 17, 23, 4, 5, 22, 16, 8, 9, 20, 19, 14, 15, 21, 18],
   .tau,
   .tau,
   .xi,
   .rho (false, 0, 12),
   .perm #[6, 22, 2, 3, 0, 9, 17, 14, 1, 11, 13, 16, 20, 5, 8, 10, 23, 18, 19, 7, 21, 15, 4, 12],
   .xi,
   .rho (false, 0, 24),
   .perm #[6, 7, 2, 3, 10, 11, 14, 15, 0, 1, 4, 5, 12, 13, 8, 9, 22, 19, 23, 18, 16, 20, 21, 17]]

@[expose] def thirteenK : List Native.Gen :=
  [.tau,
   .tau,
   .rho (false, 1695, 2495),
   .tau,
   .rho (false, 1790, 2343),
   .rho (false, 0, 1560),
   .rho (false, 0, 60),
   .perm #[19, 12, 17, 1, 10, 7, 18, 22, 14, 0, 6, 5, 20, 15, 2, 21, 4, 16, 23, 9, 13, 8, 3, 11],
   .xi,
   .xi,
   .rho (false, 0, 2),
   .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
   .xi,
   .rho (false, 0, 14),
   .perm #[0, 2, 6, 17, 7, 15, 12, 18, 1, 20, 13, 8, 11, 16, 10, 5, 19, 21, 4, 23, 9, 3, 22, 14]]

@[expose] def thirteenKi : List Native.Gen :=
  [.tau,
   .tau,
   .rho (false, 1695, 2495),
   .tau,
   .rho (true, 1790, 2343),
   .rho (false, 0, 1560),
   .rho (false, 0, 60),
   .perm #[19, 12, 17, 1, 10, 7, 18, 22, 14, 0, 6, 5, 20, 15, 2, 21, 4, 16, 23, 9, 13, 8, 3, 11],
   .xi,
   .xi,
   .rho (false, 0, 2),
   .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
   .xi,
   .rho (false, 0, 14),
   .perm #[0, 2, 6, 17, 7, 15, 12, 18, 1, 20, 13, 8, 11, 16, 10, 5, 19, 21, 4, 23, 9, 3, 22, 14]]

@[expose] def thirteenZ : List Native.Gen :=
  [.tau,
   .tau,
   .rho (false, 1777, 216),
   .tau,
   .rho (true, 2913, 185),
   .rho (false, 0, 1536),
   .rho (false, 0, 30),
   .perm #[9, 17, 20, 19, 22, 12, 11, 14, 21, 7, 10, 4, 23, 2, 8, 3, 16, 0, 15, 6, 18, 5, 13, 1],
   .xi,
   .rho (false, 0, 58),
   .perm #[0, 5, 6, 7, 1, 2, 3, 4, 8, 16, 12, 20, 22, 14, 18, 10, 19, 11, 23, 15, 13, 21, 9, 17],
   .xi,
   .rho (false, 0, 6),
   .perm #[1, 3, 13, 15, 18, 19, 21, 22, 0, 2, 12, 14, 17, 16, 23, 20, 9, 7, 11, 5, 8, 4, 6, 10]]

@[expose] def thirteenT0 : List Native.Gen := [.rho (true, 0, 0)]

@[expose] def thirteenY : List Native.Gen := thirteenKi ++ thirteenX ++ thirteenK

@[expose] def thirteenYi : List Native.Gen := thirteenKi ++ thirteenXi ++ thirteenK

end CFSG.AGLEmbedding.Norton.MON11_13
