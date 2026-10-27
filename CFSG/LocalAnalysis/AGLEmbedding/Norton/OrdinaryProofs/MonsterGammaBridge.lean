module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporHS5
import CFSG.Sporadic.Bridge.Y322Central

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

theorem sporGammaOneAt_M_of_fusion
    {p : ℕ} (hp : p.Prime)
    (hfus : FusionGenerationOf (CFSG.Blueprint.NativeSporadic.Carrier .M) p) :
    CFSG.AGLEmbedding.SporGammaOneAt .M p := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  exact CFSG.AGLEmbedding.sporGammaOneAt_of_fusion hp ⟨b⟩ hfus

theorem sporGammaOneAt_M_eleven_of_fusion
    (hfus : FusionGenerationOf (CFSG.Blueprint.NativeSporadic.Carrier .M) 11) :
    CFSG.AGLEmbedding.SporGammaOneAt .M 11 :=
  sporGammaOneAt_M_of_fusion (by norm_num) hfus

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
