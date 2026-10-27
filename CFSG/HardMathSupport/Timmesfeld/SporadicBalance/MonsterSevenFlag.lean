module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
public import CFSG.YGroups.Y443.Native.Words

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData

@[expose] def m7hW : List Native.Gen :=
  [.tau, .tau, .rho (false, 561, 1093), .tau, .rho (false, 1067, 855), .rho (false, 0, 2843),
    .rho (false, 0, 54),
    .perm #[18, 8, 7, 6, 9, 22, 17, 20, 10, 1, 2, 16, 5, 15, 3, 21, 11, 14, 12, 19, 4, 0, 13, 23],
    .xi, .xi, .rho (false, 0, 20),
    .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
    .xi, .xi, .rho (false, 0, 48),
    .perm #[1, 3, 10, 11, 13, 14, 21, 23, 12, 15, 22, 20, 2, 0, 8, 9, 5, 19, 18, 6, 4, 16, 7, 17],
    .tau, .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
    .xi, .rho (false, 0, 52),
    .perm #[1, 4, 8, 18, 13, 22, 17, 16, 9, 19, 7, 3, 10, 11, 23, 12, 2, 15, 0, 21, 20, 5, 6, 14],
    .tau, .xi, .xi, .rho (false, 0, 24),
    .perm #[0, 6, 10, 11, 1, 7, 13, 12, 2, 5, 16, 17, 4, 3, 23, 22, 20, 18, 15, 8, 21, 19, 9, 14],
    .xi, .xi, .rho (false, 0, 54),
    .perm #[6, 7, 10, 11, 17, 21, 18, 23, 4, 8, 9, 5, 1, 12, 0, 13, 16, 20, 22, 19, 3, 2, 15, 14],
    .tau, .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 6, 8, 9, 1, 7, 15, 14, 2, 5, 18, 19, 4, 3, 21, 20, 22, 16, 13, 10, 23, 17, 11, 12],
    .xi, .xi, .rho (false, 0, 36),
    .perm #[0, 1, 12, 13, 16, 22, 19, 20, 3, 15, 14, 2, 9, 4, 8, 5, 18, 21, 23, 17, 10, 11, 6, 7],
    .tau, .xi, .xi, .rho (false, 0, 8),
    .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
    .xi, .rho (false, 0, 6),
    .perm #[4, 5, 6, 17, 7, 18, 19, 16, 8, 22, 15, 0, 2, 12, 20, 9, 14, 3, 10, 21, 23, 11, 1, 13],
    .tau, .xi, .xi, .rho (false, 0, 8),
    .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
    .xi, .rho (false, 0, 6),
    .perm #[5, 7, 8, 13, 9, 18, 14, 16, 11, 21, 23, 12, 19, 22, 1, 6, 0, 15, 10, 2, 20, 4, 17, 3],
    .tau, .xi, .rho (false, 0, 38),
    .perm #[7, 23, 2, 3, 0, 11, 17, 13, 1, 9, 14, 16, 21, 4, 10, 8, 22, 18, 19, 6, 20, 12, 5, 15],
    .xi, .rho (false, 0, 10),
    .perm #[12, 13, 2, 3, 4, 5, 10, 11, 0, 1, 14, 15, 8, 9, 6, 7, 22, 17, 20, 18, 19, 21, 23, 16]]

@[expose] def m7hPairs : List (List Native.Gen × List Native.Gen) :=
  [(wq1 ++ m7hW, m7hW ++ powL 2 wq4 ++ wq2 ++ wq1), (wq2 ++ m7hW, m7hW ++ wq3 ++ wq2),
    (wq3 ++ m7hW, m7hW ++ powL 5 wq4 ++ wq3 ++ powL 4 wq1),
    (wq4 ++ m7hW, m7hW ++ powL 3 wq4 ++ powL 2 wq1), (wq5 ++ m7hW, m7hW ++ wq5)]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag
