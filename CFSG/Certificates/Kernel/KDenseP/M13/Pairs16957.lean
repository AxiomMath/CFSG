module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbarInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenEbarData
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Pairs

public section

namespace CFSG.KC.KDenseP.M13

open CFSG.KC.KDenseP.MonThreeB CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.AGLEmbedding.Norton.GenD13

@[expose] def e16957 : Prs := ebarPairs genD13W1 imgT13 imgD13

end CFSG.KC.KDenseP.M13

end
