module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3KFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.SylowThreeAbelian.L28
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.SylowThreeAbelian.L34

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2


theorem kFactSylowThreeAbelian_holds : KFactSylowThreeAbelian := by
  refine ⟨?_, SylowThreeAbelian.kFactSylowThreeAbelian_psl28⟩
  intro d hd X _ _ K R hKn hC ⟨e⟩ hcomm ⟨E, hER, hE, hE9⟩
  have : K.Normal := hKn
  obtain ⟨θ⟩ := nonempty_equiv_S_of_index hd e
  exact SylowThreeAbelian.kFactSylowThreeAbelian_l34 hC θ R hcomm hER hE hE9

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
