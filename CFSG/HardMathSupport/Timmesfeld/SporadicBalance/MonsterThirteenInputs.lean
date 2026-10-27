module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenInputs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

open CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

@[expose] def vW13 : List Native.Gen := [Native.Gen.rho (true, 0, 0)]

@[expose] def tW13 : List Native.Gen :=
  [.tau, .tau, .rho (false, 1199, 813), .tau, .rho (false, 2727, 40), .rho (false, 0, 302),
    .rho (false, 0, 0),
    .perm #[15, 5, 12, 7, 1, 21, 22, 0, 9, 19, 17, 8, 6, 4, 13, 14, 18, 11, 16, 10, 23, 20, 2, 3],
    .xi, .rho (false, 0, 34),
    .perm #[0, 7, 18, 19, 1, 6, 20, 21, 2, 4, 10, 11, 5, 3, 12, 13, 15, 8, 22, 16, 14, 9, 17, 23],
    .xi, .rho (false, 0, 42),
    .perm #[0, 3, 4, 9, 7, 13, 10, 14, 8, 21, 20, 6, 1, 16, 22, 15, 19, 5, 11, 17, 18, 12, 2, 23],
    .xi]

@[expose] def wvW13 : List Native.Gen :=
  [.tau, .tau, .rho (false, 3550, 3681), .tau, .rho (true, 2552, 40), .rho (false, 0, 2331),
    .rho (false, 0, 12),
    .perm #[18, 15, 0, 3, 16, 12, 21, 20, 6, 4, 14, 19, 8, 9, 17, 13, 2, 22, 5, 11, 23, 1, 7, 10],
    .xi, .xi, .rho (false, 0, 24),
    .perm #[0, 6, 10, 11, 1, 7, 13, 12, 2, 5, 16, 17, 4, 3, 23, 22, 20, 18, 15, 8, 21, 19, 9, 14],
    .xi, .xi, .rho (false, 0, 14),
    .perm #[9, 10, 12, 17, 15, 23, 20, 18, 6, 16, 7, 14, 11, 1, 21, 5, 4, 8, 3, 22, 19, 0, 13, 2],
    .xi, .rho (false, 0, 48),
    .perm #[2, 3, 4, 7, 0, 1, 5, 6, 8, 10, 23, 21, 11, 9, 20, 22, 12, 14, 19, 17, 15, 13, 16, 18]]

@[expose] def wtW13 : List Native.Gen :=
  [.tau, .tau, .rho (false, 1188, 3254), .tau, .rho (true, 3731, 3200), .rho (false, 0, 3803),
    .rho (false, 0, 34),
    .perm #[10, 2, 1, 15, 17, 13, 18, 11, 21, 5, 3, 16, 20, 23, 8, 14, 12, 9, 7, 4, 19, 0, 22, 6],
    .xi, .xi, .rho (false, 0, 56),
    .perm #[0, 7, 8, 9, 1, 6, 14, 15, 2, 4, 16, 17, 5, 3, 22, 23, 21, 18, 12, 10, 20, 19, 11, 13],
    .xi, .xi, .rho (false, 0, 46),
    .perm #[3, 5, 9, 21, 15, 17, 22, 20, 8, 10, 19, 13, 11, 23, 6, 2, 16, 7, 4, 12, 0, 14, 1, 18]]

@[expose] def wvtW13 : List Native.Gen :=
  [.tau, .tau, .rho (false, 2386, 1106), .tau, .rho (true, 2806, 1353), .rho (false, 0, 2424),
    .rho (false, 0, 42),
    .perm #[22, 15, 17, 23, 19, 12, 0, 3, 5, 18, 7, 13, 20, 6, 2, 11, 14, 8, 16, 9, 4, 1, 10, 21],
    .xi, .rho (false, 0, 6),
    .perm #[0, 1, 2, 5, 3, 4, 6, 7, 8, 14, 16, 22, 23, 17, 15, 9, 18, 20, 10, 12, 13, 11, 21, 19],
    .xi, .xi, .rho (false, 0, 0),
    .perm #[1, 2, 3, 7, 10, 13, 20, 19, 0, 4, 6, 5, 16, 23, 14, 9, 12, 21, 11, 18, 22, 8, 15, 17],
    .xi, .rho (false, 0, 42),
    .perm #[0, 4, 9, 14, 1, 2, 19, 20, 3, 7, 13, 10, 6, 5, 23, 16, 12, 17, 15, 21, 11, 22, 18, 8]]

@[expose] def htW13 : List Native.Gen :=
  [.tau, .tau, .rho (false, 331, 2700), .tau, .rho (false, 501, 862), .rho (false, 0, 4017),
    .rho (false, 0, 30),
    .perm #[13, 0, 8, 4, 10, 17, 21, 11, 2, 19, 22, 3, 12, 9, 1, 5, 6, 23, 7, 18, 14, 15, 20, 16],
    .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
    .xi, .rho (false, 0, 60),
    .perm #[0, 1, 12, 22, 13, 16, 19, 20, 2, 4, 17, 11, 10, 23, 9, 14, 21, 7, 15, 5, 8, 3, 6, 18],
    .xi, .xi, .tau, .xi, .xi, .rho (false, 0, 62),
    .perm #[0, 5, 8, 9, 1, 4, 12, 13, 2, 6, 19, 18, 7, 3, 23, 22, 20, 17, 14, 10, 21, 16, 11, 15],
    .xi, .xi, .rho (false, 0, 42),
    .perm #[6, 7, 10, 21, 11, 17, 18, 23, 2, 19, 12, 5, 9, 1, 22, 3, 13, 8, 14, 20, 16, 15, 4, 0],
    .xi, .xi, .tau]

@[expose] def hvtW13 : List Native.Gen :=
  [.tau, .tau, .rho (false, 1635, 2240), .tau, .rho (false, 1762, 314), .rho (false, 0, 897),
    .rho (false, 0, 2),
    .perm #[16, 23, 7, 17, 1, 0, 22, 6, 14, 21, 13, 4, 15, 19, 10, 2, 11, 5, 9, 20, 12, 3, 8, 18],
    .xi, .rho (false, 0, 24),
    .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
    .xi, .xi, .rho (false, 0, 40),
    .perm #[8, 9, 14, 17, 15, 22, 23, 16, 0, 20, 5, 10, 12, 2, 18, 1, 4, 13, 6, 19, 21, 7, 11, 3],
    .xi, .xi, .rho (false, 0, 14),
    .perm #[1, 7, 8, 10, 0, 4, 22, 20, 2, 6, 16, 18, 5, 3, 14, 12, 13, 17, 23, 9, 15, 19, 11, 21],
    .tau, .xi, .xi, .rho (false, 0, 20),
    .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
    .xi, .xi, .rho (false, 0, 14),
    .perm #[2, 3, 14, 16, 15, 20, 19, 22, 5, 12, 18, 6, 7, 23, 1, 9, 17, 10, 8, 13, 0, 4, 11, 21],
    .xi, .xi, .tau, .tau]

@[expose] def vtW13 : List Native.Gen := vW13 ++ tW13

@[expose] def bW13 : List Native.Gen := genD13W0 ++ powL 9 genD13W2 ++ powL 5 genD13W1

@[expose] def bpW13 : List Native.Gen := genD13W0 ++ powL 5 genD13W2 ++ powL 10 genD13W1

@[expose] def thirteenBPairs : List (List Native.Gen × List Native.Gen) :=
  [(genD13W1 ++ vW13, vW13 ++ genD13W1),
    (powL 7 genD13W0 ++ vW13 ++ powL 6 genD13W0 ++ vW13, genD13W0),
    (powL 7 genD13W2 ++ vW13 ++ powL 6 genD13W2 ++ vW13, powL 4 genD13W1 ++ genD13W2),
    (tW13 ++ tW13, []),
    (tW13 ++ vW13, vW13 ++ tW13),
    (genD13W1 ++ tW13 ++ genD13W1 ++ tW13, []),
    (tW13 ++ bW13, bW13 ++ tW13),
    (vtW13 ++ bpW13, bpW13 ++ vtW13),
    (powL 4 wvW13, []),
    (wvW13 ++ vW13, vW13 ++ wvW13),
    (wvW13 ++ genD13W1, genD13W1 ++ wvW13),
    (powL 4 wtW13, []),
    (wtW13 ++ tW13, tW13 ++ wtW13),
    (wtW13 ++ bW13, bW13 ++ wtW13),
    (genD13W1 ++ wtW13, wtW13 ++ powL 8 genD13W1),
    (powL 4 wvtW13, []),
    (wvtW13 ++ vtW13, vtW13 ++ wvtW13),
    (wvtW13 ++ bpW13, bpW13 ++ wvtW13),
    (genD13W1 ++ wvtW13, wvtW13 ++ powL 8 genD13W1),
    (tW13 ++ htW13, htW13 ++ vW13),
    (vtW13 ++ hvtW13, hvtW13 ++ vW13)]

@[expose] def thirteenBDataCheck (_ : Unit := ()) : Bool :=
  agreeAll thirteenBPairs && movesSome tW13 && movesSome vtW13 && movesSome bW13 &&
    movesSome bpW13 && movesSome (wvW13 ++ wvW13) && movesSome (wtW13 ++ wtW13) &&
    movesSome (wvtW13 ++ wvtW13)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
