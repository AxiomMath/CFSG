module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairRankOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitness
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryRealizationTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

universe u

variable {G : Type u} [Group G] [Finite G]

theorem highRankPairWitnessTheorem
    (hgen : PairGenerationTheorem G) :
    HighRankPairWitnessTheorem G :=
  fun _ _ h _ hbeta _ ht hrank => high_rank_pair_witness hgen (noncentral_pair_action
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) suzukiOuterOdd
      unitaryAutomorphismRealization) h
    (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) hbeta ht hrank

theorem pairStabilizerRankOneTheorem_of_generation
    (hgen : PairGenerationTheorem G) :
    PairStabilizerRankOneTheorem G :=
  pairStabilizerRankOneTheorem (highRankPairWitnessTheorem hgen) (noncentral_pair_action
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) suzukiOuterOdd
      unitaryAutomorphismRealization)

end CFSG.ProperTwoGeneratedCore.HighRankPair
