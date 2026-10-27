module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRel

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

open CFSG.Monster.AxisCount

@[expose, irreducible] def m5tW : List Native.Gen :=
  [.tau, .tau, .rho (false, 850, 502), .tau, .rho (false, 1740, 468), .rho (false, 0, 1676),
    .rho (false, 0, 10),
    .perm #[7, 0, 3, 2, 15, 9, 21, 19, 6, 1, 5, 4, 8, 14, 18, 20, 16, 12, 22, 10, 23, 13, 11, 17],
    .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 9, 1, 5, 13, 12, 2, 7, 17, 16, 6, 3, 20, 21, 23, 19, 15, 10, 22, 18, 11, 14],
    .xi, .rho (false, 0, 0),
    .perm #[2, 6, 8, 20, 12, 21, 18, 23, 0, 1, 13, 17, 16, 9, 11, 14, 7, 19, 4, 15, 5, 10, 22, 3],
    .xi, .xi, .tau, .tau, .xi, .rho (false, 0, 36),
    .perm #[0, 5, 14, 15, 1, 4, 10, 11, 2, 6, 21, 20, 7, 3, 17, 16, 18, 23, 8, 12, 19, 22, 13, 9],
    .xi, .rho (false, 0, 28),
    .perm #[2, 3, 5, 10, 7, 9, 18, 17, 6, 8, 20, 22, 13, 12, 11, 4, 23, 14, 0, 19, 16, 1, 21, 15],
    .tau, .tau, .xi, .rho (false, 0, 24),
    .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
    .xi, .rho (false, 0, 0),
    .perm #[4, 5, 6, 8, 7, 10, 9, 11, 0, 17, 22, 15, 12, 23, 19, 3, 20, 14, 1, 18, 16, 2, 13, 21],
    .tau, .xi, .xi, .rho (false, 0, 8),
    .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
    .xi, .rho (false, 0, 20),
    .perm #[6, 7, 8, 10, 13, 21, 14, 20, 16, 18, 1, 2, 12, 22, 23, 15, 19, 3, 17, 0, 4, 11, 9, 5],
    .tau, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 9, 1, 5, 13, 12, 2, 7, 17, 16, 6, 3, 20, 21, 23, 19, 15, 10, 22, 18, 11, 14],
    .xi, .xi, .rho (false, 0, 34),
    .perm #[5, 7, 8, 23, 10, 19, 18, 20, 0, 9, 3, 22, 16, 1, 4, 15, 14, 17, 2, 6, 11, 13, 21, 12],
    .xi, .tau, .tau, .xi, .rho (false, 0, 34),
    .perm #[0, 7, 18, 19, 1, 6, 20, 21, 2, 4, 10, 11, 5, 3, 12, 13, 15, 8, 22, 16, 14, 9, 17, 23],
    .xi, .rho (false, 0, 4),
    .perm #[2, 4, 6, 14, 7, 18, 21, 9, 3, 13, 20, 23, 16, 15, 17, 1, 8, 12, 0, 10, 22, 5, 11, 19]]

@[expose] def m5tImg : Array (Array Nat) :=
  #[#[0, 0, 0, 0, 1, 0, 0, 3, 0],
    #[0, 0, 3, 4, 0, 0, 3, 0, 0],
    #[0, 0, 1, 2, 4, 2, 0, 1, 0],
    #[0, 0, 3, 0, 0, 1, 0, 2, 0],
    #[0, 0, 4, 0, 0, 0, 0, 0, 4],
    #[0, 0, 1, 0, 0, 2, 3, 0, 3],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def m5tEqs : List (List Native.Gen × List Native.Gen) :=
  (List.range 7).map fun i => (fiveGens[i + 2]! ++ m5tW, m5tW ++ rhsW (m5tImg[i]!))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
