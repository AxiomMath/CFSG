module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreRee

public section

namespace CFSG.AGLEmbedding

theorem kFactRankOneCoreProper :
    KFactRankOneCoreProper := by
  intro L _ _ p hp hp2 d hd h T
  have : Fact p.Prime := ⟨hp⟩
  rcases hd with ⟨n, q, hdq, hqp, hqn⟩ | hu | ⟨hp3, hm⟩
  · exact (KFactProofs.RankOneCore.rankOneCoreData_linTwo hp2 (hqn ▸ q.exponent_pos)
      ⟨q, hdq, hqp, hqn⟩ h T).glbCore_ne_top hp.two_le
  · exact (KFactProofs.RankOneCore.rankOneCoreData_unitary hu h T).glbCore_ne_top hp.two_le
  · subst hp3
    exact (KFactProofs.RankOneCore.rankOneCoreData_ree ⟨rfl, hm⟩ h T).glbCore_ne_top
      hp.two_le

end CFSG.AGLEmbedding
