module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9652

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.SectionRank CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.Open

theorem glbCore_Th_five [Finite (NativeSporadic.Carrier .Th)] :
    ∀ S : Sylow 5 (NativeSporadic.Carrier .Th),
      GLBCore 5 2 (S : Subgroup (NativeSporadic.Carrier .Th)) = ⊤ := by
  intro S
  have : Finite NativeSporadic.Th := ‹Finite (NativeSporadic.Carrier .Th)›
  exact glbCore_two_eq_top_of_coreGenCheck (spec2 248) (D := CoreTh5.spec)
    (by show Nat.Prime 5; norm_num) Certificates.certificate9652 S

end CFSG.AGLEmbeddingD2
