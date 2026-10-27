module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Datum
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Fi23
public import CFSG.Sporadic.FischerOddCore.Fi23Aut

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint

theorem d2IndexDatum_Fi23_five
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .Fi23) :
    D2IndexDatum L 5 :=
  d2IndexDatum_of_fusion e Nat.prime_five (by norm_num)
    (CFSG.Sporadic.FischerOddCore.CTUC_Fi23_Schreier.1.le.trans (by norm_num))
    (by
      rw [show Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 from
        CFSG.Sporadic.Fi23.card_Fi23]
      norm_num)
    CFSG.AGLEmbedding.fusionGenerationOf_Fi23_five

end CFSG.AGLEmbeddingD2
