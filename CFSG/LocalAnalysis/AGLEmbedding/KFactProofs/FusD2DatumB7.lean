module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Datum
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BRowsOf
public import CFSG.Sporadic.Bridge.BFusSevenMain

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint

theorem d2IndexDatum_B_seven
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .B) :
    D2IndexDatum L 7 :=
  d2IndexDatum_of_fusion e Nat.prime_seven (by norm_num)
    (CFSG.RankThree.PartOne.SPOR.card_outer_B.le.trans (by norm_num))
    (by
      rw [CFSG.AGLEmbedding.card_B_carrier]
      norm_num)
    CFSG.Sporadic.Bridge.B.fusionGenerationOf_B_seven

end CFSG.AGLEmbeddingD2
