module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBWords
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenInputs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

open CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

@[expose] def j1W : List Native.Gen :=
  [.rho (false, 0, 0),
    .perm #[8, 10, 9, 11, 4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 13, 15, 16, 17, 19, 18, 20, 23, 22, 21]]

@[expose] def j2W : List Native.Gen :=
  [.rho (false, 0, 0),
    .perm #[0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15, 20, 22, 21, 23, 16, 18, 17, 19]]

@[expose] def tj1W : List Native.Gen :=
  [.tau, .tau, .rho (false, 2478, 1745), .tau, .rho (false, 960, 3123), .rho (false, 0, 396),
    .rho (false, 0, 24),
    .perm #[0, 3, 9, 11, 21, 13, 12, 22, 1, 8, 2, 10, 16, 7, 6, 18, 19, 17, 5, 4, 20, 14, 23, 15],
    .xi, .rho (false, 0, 40),
    .perm #[9, 10, 2, 3, 0, 1, 8, 11, 4, 6, 16, 19, 17, 18, 7, 5, 15, 13, 22, 23, 20, 21, 12, 14],
    .tau, .tau, .xi, .xi, .rho (false, 0, 0),
    .perm #[0, 4, 2, 3, 1, 5, 7, 6, 8, 13, 19, 22, 12, 9, 23, 18, 20, 17, 15, 10, 16, 21, 11, 14],
    .tau, .tau]

@[expose] def tj2W : List Native.Gen :=
  [.tau, .tau, .rho (false, 3689, 3368), .tau, .rho (true, 1625, 64), .rho (false, 0, 3969),
    .rho (false, 0, 30),
    .perm #[14, 6, 7, 5, 15, 12, 13, 4, 10, 18, 22, 0, 1, 21, 16, 11, 17, 8, 2, 23, 20, 3, 9, 19],
    .xi, .rho (false, 0, 0),
    .perm #[20, 21, 2, 3, 0, 1, 22, 23, 4, 5, 18, 19, 16, 17, 6, 7, 11, 8, 13, 15, 14, 12, 10, 9],
    .tau, .xi, .xi, .rho (false, 0, 12),
    .perm #[4, 5, 2, 3, 0, 1, 6, 7, 8, 9, 14, 15, 12, 13, 10, 11, 17, 16, 23, 22, 21, 20, 19, 18],
    .tau, .xi, .rho (false, 0, 20),
    .perm #[13, 22, 2, 3, 0, 4, 19, 8, 1, 6, 11, 16, 21, 14, 5, 7, 20, 17, 18, 12, 23, 9, 15, 10]]

@[expose] def tj12W : List Native.Gen :=
  [.tau, .tau, .rho (false, 1847, 1326), .tau, .rho (true, 3732, 468), .rho (false, 0, 3841),
    .rho (false, 0, 10),
    .perm #[3, 1, 11, 9, 23, 22, 18, 17, 2, 0, 10, 8, 20, 21, 16, 19, 13, 7, 15, 5, 12, 4, 6, 14],
    .xi, .xi, .rho (false, 0, 40),
    .perm #[9, 10, 2, 3, 0, 1, 8, 11, 4, 6, 16, 19, 17, 18, 7, 5, 15, 13, 22, 23, 20, 21, 12, 14],
    .tau, .xi, .xi, .rho (false, 0, 0),
    .perm #[0, 4, 2, 3, 1, 5, 7, 6, 8, 13, 19, 22, 12, 9, 23, 18, 20, 17, 15, 10, 16, 21, 11, 14],
    .tau, .tau]

@[expose] def censusGW : List Native.Gen :=
  [.tau, .tau, .rho (false, 1212, 849), .tau, .rho (false, 3372, 2337), .rho (false, 0, 1736),
    .rho (false, 0, 58),
    .perm #[21, 9, 17, 8, 1, 19, 22, 0, 13, 12, 20, 16, 7, 14, 11, 3, 23, 18, 4, 5, 10, 2, 15, 6],
    .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 8, 9, 1, 5, 13, 12, 2, 7, 17, 16, 6, 3, 20, 21, 23, 19, 15, 10, 22, 18, 11, 14],
    .xi, .rho (false, 0, 2),
    .perm #[8, 11, 13, 17, 14, 23, 20, 18, 0, 10, 4, 21, 16, 7, 15, 6, 1, 19, 3, 12, 9, 5, 22, 2],
    .xi, .rho (false, 0, 6),
    .perm #[0, 1, 2, 5, 3, 4, 6, 7, 8, 14, 16, 22, 23, 17, 15, 9, 18, 20, 10, 12, 13, 11, 21, 19]]

structure CensusLine where
  a : ℕ
  b : ℕ
  xw : List Bool
  corrG : Bool
  j : ℕ
  toC : Bool
  lam : ℕ

@[expose] def censusLines : List CensusLine :=
  [
    ⟨1, 0, [true], false, 0, false, 4⟩,
    ⟨1, 1, [true, false, false], false, 10, false, 11⟩,
    ⟨1, 2, [true, false], false, 10, false, 9⟩,
    ⟨1, 3, [false], false, 7, false, 6⟩,
    ⟨1, 4, [true, false], true, 6, true, 11⟩,
    ⟨1, 5, [false, true], true, 12, true, 3⟩,
    ⟨1, 6, [], false, 9, false, 5⟩,
    ⟨1, 7, [true], true, 5, true, 7⟩,
    ⟨1, 8, [false, false], false, 11, false, 9⟩,
    ⟨1, 9, [false], true, 10, true, 5⟩,
    ⟨1, 10, [true, false, true], true, 6, true, 9⟩,
    ⟨1, 11, [true, false, true], false, 1, false, 6⟩,
    ⟨1, 12, [false, true], false, 9, false, 8⟩,
    ⟨0, 1, [], true, 0, true, 1⟩
  ]

@[expose] def lineRepW (e : CensusLine) : List Native.Gen := powL e.b genD13W2 ++ powL e.a genD13W0

@[expose] def lineConjW (e : CensusLine) : List Native.Gen :=
  (e.xw.map fun l => if l then genD13W3 else genD13W4).flatten ++
    powL e.j (if e.corrG then genD13W0 else genD13W2) ++ (if e.toC then genD13W6 else censusGW)

@[expose] def lineTargetW (e : CensusLine) : List Native.Gen :=
  if e.toC then genD13W1 else thirteenX

@[expose] def thirteenAPairs : List (List Native.Gen × List Native.Gen) :=
  [(j1W ++ j1W, []),
    (j2W ++ j2W, []),
    (j1W ++ j2W, j2W ++ j1W),
    (thirteenX ++ j1W, j1W ++ thirteenX),
    (thirteenX ++ j2W, j2W ++ thirteenX),
    (j1W ++ tj1W, tj1W ++ tStarW),
    (j2W ++ tj2W, tj2W ++ tStarW),
    (j1W ++ j2W ++ tj12W, tj12W ++ tStarW)] ++
  censusLines.map fun e => (lineRepW e ++ lineConjW e, lineConjW e ++ powL e.lam (lineTargetW e))

@[expose] def thirteenADataCheck (_ : Unit := ()) : Bool :=
  agreeAll thirteenAPairs && movesSome j1W && movesSome j2W && movesSome (j1W ++ j2W)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
