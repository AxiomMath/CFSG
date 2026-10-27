module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterGammaBridge
public import CFSG.Monster.Generated.Data

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)
open CFSG.Monster.Generated

theorem sporGammaOneAt_M_eleven_of_gmat
    (e : CFSG.Blueprint.NativeSporadic.Carrier .M ≃* Gmat)
    (f11 : FusionGenerationOf Gmat 11) :
    CFSG.AGLEmbedding.SporGammaOneAt .M 11 :=
  sporGammaOneAt_M_eleven_of_fusion (CFSG.AGLEmbedding.fusionGenerationOf_of_mulEquiv e.symm f11)

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
