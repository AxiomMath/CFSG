module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

open CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] def wW : List Native.Gen :=
  [.rho (false, 1374, 2577), .rho (false, 0, 1599)]

@[expose] def twW : List Native.Gen :=
  [.rho (true, 1374, 2577), .rho (false, 0, 1599)]

@[expose] def hwW : List Native.Gen :=
  [.tau, .tau, .rho (false, 1109, 3146), .tau, .rho (false, 3644, 402), .rho (false, 0, 40),
    .perm #[14, 15, 8, 9, 16, 23, 17, 22, 18, 20, 21, 19, 6, 7, 0, 1, 12, 10, 11, 13, 4, 3, 5, 2],
    .xi, .rho (false, 0, 36),
    .perm #[0, 5, 14, 15, 1, 4, 10, 11, 2, 6, 21, 20, 7, 3, 17, 16, 18, 23, 8, 12, 19, 22, 13, 9],
    .xi, .rho (false, 0, 14),
    .perm #[6, 7, 14, 20, 15, 16, 23, 18, 3, 19, 5, 9, 1, 12, 22, 2, 4, 0, 11, 17, 21, 10, 8, 13],
    .xi, .xi, .tau]

@[expose] def htwW : List Native.Gen :=
  [.tau, .tau, .rho (false, 1109, 3146), .tau, .rho (false, 3644, 402), .rho (false, 0, 40),
    .perm #[14, 15, 8, 9, 16, 23, 17, 22, 18, 20, 21, 19, 6, 7, 0, 1, 12, 10, 11, 13, 4, 3, 5, 2],
    .xi, .rho (false, 0, 36),
    .perm #[0, 5, 14, 15, 1, 4, 10, 11, 2, 6, 21, 20, 7, 3, 17, 16, 18, 23, 8, 12, 19, 22, 13, 9],
    .xi, .rho (false, 0, 14),
    .perm #[6, 7, 14, 20, 15, 16, 23, 18, 3, 19, 5, 9, 1, 12, 22, 2, 4, 0, 11, 17, 21, 10, 8, 13],
    .xi, .xi, .tau, .tau]

@[expose] def w0W : List Native.Gen :=
  [.tau, .tau, .rho (false, 2130, 2160), .tau, .rho (false, 1106, 1240), .rho (false, 0, 3683),
    .rho (false, 0, 24),
    .perm #[9, 4, 8, 5, 17, 18, 23, 21, 16, 20, 22, 19, 14, 3, 15, 2, 12, 13, 0, 1, 11, 7, 6, 10],
    .xi, .xi, .rho (false, 0, 20),
    .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
    .xi, .xi, .rho (false, 0, 8),
    .perm #[1, 3, 13, 16, 15, 23, 20, 17, 4, 19, 5, 14, 2, 11, 22, 6, 7, 0, 8, 21, 18, 10, 12, 9],
    .xi]

@[expose] def e0W : List Native.Gen :=
  [.rho (false, 1036, 655), .rho (false, 0, 3364)]

@[expose] def tW : List Native.Gen := [Native.Gen.rho (true, 0, 0)]

@[expose] def elevenPairs : List (List Native.Gen × List Native.Gen) :=
  [(gen11W1 ++ gen11W2, gen11W2 ++ powL 4 gen11W1 ++ powL 4 gen11W0),
    (wW ++ gen11W0, gen11W0 ++ wW),
    (wW ++ hwW, hwW ++ tW),
    (twW ++ htwW, htwW ++ tW),
    (powL 3 w0W, []),
    (w0W ++ gen11W0, gen11W0 ++ w0W),
    (w0W ++ tW, tW ++ w0W),
    (e0W ++ gen11W0, gen11W0 ++ e0W)]

@[expose] def commW : List Native.Gen := powL 2 w0W ++ e0W ++ w0W ++ e0W

@[expose] def movesSome (w : List Native.Gen) : Bool :=
  EdgeNoncomm.moveCheck w (aV ()) || EdgeNoncomm.moveCheck w (bV ()) ||
    EdgeNoncomm.moveCheck w (wV ())

@[expose] def elevenDataCheck (_ : Unit := ()) : Bool :=
  agreeAll elevenPairs && movesSome w0W && movesSome commW

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
