module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2KFactLeavesCoreF
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LeavesTwoK
public import CFSG.CGT.A8S.Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem d2KFactLeavesCoreF_of_seitz_solomonTimmesfeld
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hNA : CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainNonAbelian) :
    D2KFactLeavesCoreF :=
  ⟨hS, BlockB.asc81bNineThree_holds,
    (CFSG.AGLEmbeddingD2.aschbacherTwoK_solomonK_of_remaining CFSG.CGT.A8S.a8SylowInput hNA).1,
    (CFSG.AGLEmbeddingD2.aschbacherTwoK_solomonK_of_remaining CFSG.CGT.A8S.a8SylowInput hNA).2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
