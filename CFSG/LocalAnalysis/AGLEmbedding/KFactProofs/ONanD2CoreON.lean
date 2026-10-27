module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9514

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.SectionRank CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.Open

theorem glbCore_ON_seven [Finite (NativeSporadic.Carrier .ONan)] :
    ∀ S : Sylow 7 (NativeSporadic.Carrier .ONan),
      GLBCore 7 2 (S : Subgroup (NativeSporadic.Carrier .ONan)) = ⊤ := by
  intro S
  have : Finite NativeSporadic.ON := ‹Finite (NativeSporadic.Carrier .ONan)›
  exact glbCore_two_eq_top_of_coreGenCheck (spec3 154) (D := CoreON7.spec)
    (by show Nat.Prime 7; norm_num) Certificates.certificate9514 S

end CFSG.AGLEmbeddingD2
