module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbarInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Pairs

public section

namespace CFSG.KC.KDenseP.E11

open CFSG.KC.KDenseP.MonThreeB CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.AGLEmbedding.Norton.Gen11

@[expose] def e16953 : Prs := ebarPairs gen11W0 imgT11 imgD11

end CFSG.KC.KDenseP.E11

end
