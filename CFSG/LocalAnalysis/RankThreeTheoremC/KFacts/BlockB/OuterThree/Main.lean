module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.Centre
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3KFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentrePSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.NineThreeTwoResidueProof
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem OuterThree.kFactBlockOuterThree_of_inputs (h93 : Asc81bNineThree)
    (hLF : LargeFieldParabolic) (hU : OutU33) (hGA : GriessAllModelsStatement)
    (hT : CitedBlockTransvectionPLType) (hCP : KFactBlockCentrePLRank) :
    KFactBlockOuterThree := by
  intro G _ _ M S L hK hA _ hL hX hS hsolv hM3
  have hconc := h93 G M S L hK hA hL
  have hr : Open.pRank 3 L ≤ 3 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hL.le).trans hM3
  exact ⟨OuterThree.clauseO_of_nineThreeConclusion hLF hU hGA hT hK hA hL hX hS hconc hsolv hr,
    OuterThree.exists_noncentral_three_of_nineThreeConclusion hCP hT hK hA hL hX hS hconc hsolv⟩

section Certificates


theorem kFactBlockOuterThree_holds
    : KFactBlockOuterThree :=
  OuterThree.kFactBlockOuterThree_of_inputs asc81bNineThree_holds largeFieldParabolic_proved
    outU33_proved CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
    (kFactBlockCentrePLRank_of_parts OrdinaryProofs.kFactBlockCentreNine_proved
      (kFactBlockCentreRankTwo_proved
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds))

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
