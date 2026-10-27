module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenAInputs
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Pairs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenInputs

public section

namespace CFSG.KC.KDenseP.M13

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.YGroups.Y443 CFSG.KC.KDenseP.MonThreeB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

@[expose] def s0sqW13 : List Native.Gen := powL 11 genD13W1 ++ powL 5 genD13W2 ++ powL 3 genD13W0

@[expose] def e16959 : Prs :=
  thirteenAPairs.take 8 ++ [(s0sqW13 ++ censusGW, censusGW ++ thirteenX ++ thirteenX)]

@[expose] def n16959 : Prs :=
  [(.tau :: j1W, [.tau]), (.tau :: j2W, [.tau]), (.tau :: (j1W ++ j2W), [.tau])]

end CFSG.KC.KDenseP.M13

end
