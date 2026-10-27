module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeCtx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeKill

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding

theorem kFactNineThreeThreeTwo_of_tplt (hT : CitedBlockTransvectionPLType) :
    KFactNineThreeThreeTwo := fun _ _ _ _ _ _ hK hA hL hX hS h3 hr h6 =>
  not_blockPLThreeSolv_of_type hT ⟨hK, hA, hX, hS⟩ hL h3 hr h6

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
