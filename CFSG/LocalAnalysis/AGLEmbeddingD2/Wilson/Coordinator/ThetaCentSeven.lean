module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSeven
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaSevenL52
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaSevenU54

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

theorem k423ThetaCentSeven :
    CFSG.RankThree.PartTwo.Sec4.K423ThetaCentSeven := by
  intro X _ _ hX b hb3 hb1
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact thetaCent_of_l52 e b hb3 hb1
  · exact U54.thetaCent_of_u54 e b hb3 hb1

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
