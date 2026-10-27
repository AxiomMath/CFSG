module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporHS5
public import CFSG.Sporadic.Bridge.BFusSevenMain

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Open

theorem sporGammaOneAt_B_seven
    : SporGammaOneAt .B 7 :=
  sporGammaOneAt_of_fusion Nat.prime_seven CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
    CFSG.Sporadic.Bridge.B.fusionGenerationOf_B_seven

end CFSG.AGLEmbedding
