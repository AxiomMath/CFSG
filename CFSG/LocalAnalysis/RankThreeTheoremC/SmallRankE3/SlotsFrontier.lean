module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Holds
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxCount
public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614 (KFact64ii KFact64iiThree KFact292)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Frontier

theorem slotP614Three_of_frontier
    (hK64 : KFact64iiThree) : SlotP614Three :=
  slotP614Three_of Parrott.P614.slotP614CaseDelta_holds
    (Parrott.P614.slotP614Core_of_kFact64iiThree hK64)

end Frontier

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
