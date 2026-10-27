module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenData

public section

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] def xW : List Native.Gen :=
  [.tau, .tau, .rho (false, 1128, 3170), .tau, .rho (false, 815, 2938), .rho (false, 0, 498),
  .rho (false, 0, 24),
  .perm #[11, 0, 9, 22, 18, 8, 14, 4, 17, 7, 15, 10, 5, 1, 6, 20, 12, 13, 21, 3, 16, 2, 23, 19],
  .xi, .xi, .rho (false, 0, 2),
  .perm #[0, 4, 8, 9, 1, 5, 13, 12, 2, 7, 17, 16, 6, 3, 20, 21, 23, 19, 15, 10, 22, 18, 11, 14],
  .xi, .rho (false, 0, 58),
  .perm #[1, 5, 6, 7, 11, 14, 21, 16, 8, 19, 13, 22, 9, 23, 18, 12, 4, 0, 2, 3, 10, 15, 20, 17]]


@[expose] def gW : List Native.Gen :=
  [.tau, .tau, .rho (false, 1432, 3096), .tau, .rho (false, 2357, 3355), .rho (false, 0, 455),
  .rho (false, 0, 10),
  .perm #[22, 9, 23, 6, 2, 8, 1, 4, 20, 12, 3, 16, 0, 15, 21, 18, 10, 19, 5, 17, 7, 14, 11, 13],
  .xi, .xi, .rho (false, 0, 62),
  .perm #[0, 5, 8, 9, 1, 4, 12, 13, 2, 6, 19, 18, 7, 3, 23, 22, 20, 17, 14, 10, 21, 16, 11, 15],
  .xi, .xi, .rho (false, 0, 32),
  .perm #[4, 7, 8, 23, 11, 17, 22, 19, 9, 12, 14, 20, 18, 13, 0, 6, 2, 21, 10, 3, 15, 5, 16, 1],
  .xi, .rho (false, 0, 0),
  .perm #[0, 1, 2, 4, 3, 5, 7, 6, 8, 15, 18, 21, 20, 19, 14, 9, 16, 23, 10, 13, 12, 11, 22, 17]]


@[expose] def iW : List Native.Gen :=
  [.tau, .tau, .rho (false, 2149, 1954), .tau, .rho (true, 2596, 2605), .rho (false, 0, 3623),
  .rho (false, 0, 58),
  .perm #[20, 4, 1, 2, 0, 9, 14, 19, 8, 3, 12, 16, 21, 6, 11, 10, 15, 5, 22, 13, 18, 7, 17, 23],
  .xi, .rho (false, 0, 6),
  .perm #[0, 2, 3, 6, 1, 4, 7, 5, 8, 15, 16, 23, 21, 18, 13, 10, 19, 20, 11, 12, 14, 9, 22, 17],
  .xi, .xi, .rho (false, 0, 48),
  .perm #[0, 1, 5, 7, 12, 15, 22, 21, 2, 3, 6, 4, 13, 14, 23, 20, 17, 8, 18, 11, 16, 10, 9, 19],
  .tau, .tau, .xi, .rho (false, 0, 6),
  .perm #[0, 1, 2, 6, 3, 4, 7, 5, 8, 17, 20, 13, 14, 23, 18, 11, 21, 12, 9, 16, 19, 10, 15, 22],
  .xi, .rho (false, 0, 14),
  .perm #[3, 7, 9, 12, 14, 15, 18, 22, 0, 17, 1, 20, 5, 16, 21, 4, 2, 6, 13, 8, 11, 10, 19, 23],
  .xi, .tau, .tau, .xi, .rho (false, 0, 34),
  .perm #[0, 7, 18, 19, 1, 6, 20, 21, 2, 4, 10, 11, 5, 3, 12, 13, 15, 8, 22, 16, 14, 9, 17, 23],
  .xi, .rho (false, 0, 38),
  .perm #[1, 6, 10, 13, 18, 23, 20, 22, 3, 4, 8, 15, 21, 16, 17, 19, 2, 14, 5, 9, 0, 11, 12, 7],
  .xi, .tau, .tau, .xi, .xi, .rho (false, 0, 48),
  .perm #[0, 6, 7, 10, 1, 11, 13, 12, 2, 23, 9, 20, 18, 14, 22, 5, 8, 19, 3, 17, 16, 4, 21, 15],
  .xi, .tau, .tau, .xi, .xi, .rho (false, 0, 20),
  .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
  .xi, .xi, .rho (false, 0, 52),
  .perm #[6, 7, 12, 17, 13, 19, 20, 23, 4, 21, 8, 1, 11, 3, 22, 5, 9, 10, 14, 16, 18, 15, 0, 2],
  .tau, .tau, .xi, .xi, .rho (false, 0, 24),
  .perm #[0, 6, 10, 11, 1, 7, 13, 12, 2, 5, 16, 17, 4, 3, 23, 22, 20, 18, 15, 8, 21, 19, 9, 14],
  .xi, .xi, .rho (false, 0, 18),
  .perm #[10, 11, 12, 17, 13, 22, 23, 16, 4, 19, 6, 15, 9, 1, 21, 5, 7, 8, 2, 20, 18, 3, 14, 0],
  .tau, .tau, .xi, .xi, .rho (false, 0, 18),
  .perm #[0, 7, 10, 11, 1, 6, 12, 13, 2, 4, 18, 19, 5, 3, 20, 21, 23, 16, 14, 8, 22, 17, 9, 15],
  .xi, .xi, .rho (false, 0, 34),
  .perm #[2, 3, 4, 21, 5, 19, 20, 18, 12, 22, 6, 15, 9, 1, 17, 13, 7, 8, 10, 23, 16, 11, 14, 0],
  .tau, .tau, .xi, .xi, .rho (false, 0, 20),
  .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
  .xi, .xi, .rho (false, 0, 34),
  .perm #[6, 7, 14, 23, 15, 18, 20, 16, 11, 22, 13, 9, 1, 4, 19, 10, 12, 0, 3, 21, 17, 2, 8, 5]]


@[expose] def yW : List Native.Gen := xW ++ eW ++ eW

@[expose] def sevenXPairs : List (List Native.Gen × List Native.Gen) :=
  [(powL 7 xW, []), (xW ++ dW, dW ++ xW), (xW ++ zW, zW ++ xW), (tW ++ xW, xW ++ tW),
    (xW ++ eW, eW ++ xW ++ powL 3 zW)]

@[expose] def sevenYPairs : List (List Native.Gen × List Native.Gen) :=
  [(powL 7 yW, [])]

@[expose] def sevenIPairs : List (List Native.Gen × List Native.Gen) :=
  [(iW ++ dW, dW ++ iW), (iW ++ yW, yW ++ iW)]

@[expose] def sevenGPairs : List (List Native.Gen × List Native.Gen) :=
  [(dW ++ gW, gW ++ dW ++ powL 3 xW), (xW ++ gW, gW ++ powL 3 dW ++ powL 6 xW)]

@[expose] def sevenNeXWord (k : ℕ) : List Native.Gen := powL ((7 - k) % 7) dW ++ xW

@[expose] def sevenNeYWord (k : ℕ) : List Native.Gen := powL ((7 - k) % 7) dW ++ yW

end CFSG.AGLEmbedding.Norton.MON5_7
