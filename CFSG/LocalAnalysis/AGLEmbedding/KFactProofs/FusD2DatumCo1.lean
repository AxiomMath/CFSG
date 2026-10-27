module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Datum
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Co1
public import CFSG.Sporadic.Co1

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint

theorem d2IndexDatum_Co1_seven
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .Co1) :
    D2IndexDatum L 7 :=
  d2IndexDatum_of_fusion e Nat.prime_seven (by norm_num)
    (CFSG.RankThree.PartOne.SPOR.card_outer_Co1.le.trans (by norm_num))
    (by
      rw [show Nat.card (NativeSporadic.Carrier .Co1) = 4157776806543360000 from
        CFSG.Sporadic.Co1.card_Co1]
      norm_num)
    CFSG.AGLEmbedding.fusionGenerationOf_Co1_seven

end CFSG.AGLEmbeddingD2
