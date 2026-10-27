module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Datum
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Fi24prime
public import CFSG.Sporadic.Schreier.Fi24Schreier

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint

theorem d2IndexDatum_Fi24Prime_five
    {L : Type} [Group L] [Finite L] (e : L ≃* NativeSporadic.Carrier .Fi24Prime) :
    D2IndexDatum L 5 :=
  d2IndexDatum_of_fusion e Nat.prime_five (by norm_num)
    CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime.le
    (by
      rw [show Nat.card (NativeSporadic.Carrier .Fi24Prime) = 1255205709190661721292800 from
        CFSG.Sporadic.Fi24.card_Fi24prime]
      norm_num)
    CFSG.AGLEmbedding.fusionGenerationOf_Fi24prime_five

end CFSG.AGLEmbeddingD2
