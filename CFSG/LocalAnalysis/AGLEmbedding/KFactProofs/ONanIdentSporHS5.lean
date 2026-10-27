module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporDefs
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Sporadic.Bridge.HSSurj
public import Certificates.Certificate9720

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint CFSG.Open

theorem hs_fusHSFive_check :
    fusCheck (ops2 20) NativeSporadic.HSSeed1 NativeSporadic.HSSeed2
      fusHSFiveN fusHSFiveProg fusHSFive = true :=
  Certificates.certificate9720

theorem fusionGenerationOf_HS_five :
    FusionGenerationOf NativeSporadic.HS 5 :=
  fusionGenerationOf_of_check (spec2 20) (D := fusHSFive) Nat.prime_five hs_fusHSFive_check

theorem sporGammaOneAt_of_fusion {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (hfus : FusionGenerationOf (NativeSporadic.Carrier s) p) : SporGammaOneAt s p := by
  intro K _ _ ⟨e⟩ T
  obtain ⟨f⟩ := hbr
  exact glbCore_one_eq_top_of_fusionGenerationOf hp
    (fusionGenerationOf_of_mulEquiv (e.trans f.symm).symm hfus) T

theorem sporGammaOneAt_HS_five :
    SporGammaOneAt .HS 5 :=
  sporGammaOneAt_of_fusion Nat.prime_five CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
    fusionGenerationOf_HS_five

end CFSG.AGLEmbedding
