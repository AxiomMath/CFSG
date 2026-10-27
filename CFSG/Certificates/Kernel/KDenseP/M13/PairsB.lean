module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenInputs
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Pairs

public section

namespace CFSG.KC.KDenseP.M13

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.KC.KDenseP.MonThreeB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

@[expose] def b3W13 : List Native.Gen := powL 10 genD13W1 ++ genD13W2 ++ powL 3 genD13W0

@[expose] def bp3W13 : List Native.Gen := powL 7 genD13W1 ++ powL 2 genD13W2 ++ powL 3 genD13W0

@[expose] def e16958 : Prs :=
  [(tW13 ++ tW13, []),
    (tW13 ++ vW13, vW13 ++ tW13),
    (genD13W1 ++ tW13 ++ genD13W1 ++ tW13, []),
    (tW13 ++ b3W13, b3W13 ++ tW13),
    (vtW13 ++ bp3W13, bp3W13 ++ vtW13),
    (vW13 ++ vW13, []),
    (wvW13 ++ wvW13, vW13),
    (wvW13 ++ genD13W1, genD13W1 ++ wvW13),
    (wtW13 ++ wtW13, tW13),
    (wtW13 ++ b3W13, b3W13 ++ wtW13),
    (genD13W1 ++ wtW13, wtW13 ++ powL 8 genD13W1),
    (wvtW13 ++ wvtW13, vtW13),
    (wvtW13 ++ bp3W13, bp3W13 ++ wvtW13),
    (genD13W1 ++ wvtW13, wvtW13 ++ powL 8 genD13W1),
    (tW13 ++ htW13, htW13 ++ vW13),
    (vtW13 ++ hvtW13, hvtW13 ++ vW13)]

end CFSG.KC.KDenseP.M13

end
