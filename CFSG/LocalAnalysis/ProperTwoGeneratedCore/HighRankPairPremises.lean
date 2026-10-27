module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI

universe u

theorem smallerR1Full
    (G : Type u) [Group G] [Finite G] : SmallerR1Full G :=
  fun _ _ _ _ hrank ⟨A, hA⟩ => rank_two_strongEmbedding_r1Full
    (LocalCriterionRecognizedThreePoint.native_rank_two_of_two_le_twoRank hrank) A hA

theorem properStrongEmbeddingCommutingImages_holds
    (G : Type u) [Group G] [Finite G] :
    ProperStrongEmbeddingCommutingImages G :=
  properStrongEmbeddingCommutingImages G

end CFSG.ProperTwoGeneratedCore.HighRankPair
