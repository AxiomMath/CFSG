module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9654
public import Certificates.Certificate9655
public import Certificates.Certificate9656

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.SectionRank CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.Open

theorem glbCore_Fi24Prime_seven
    [Finite (NativeSporadic.Carrier .Fi24Prime)] :
    ∀ S : Sylow 7 (NativeSporadic.Carrier .Fi24Prime),
      GLBCore 7 2 (S : Subgroup (NativeSporadic.Carrier .Fi24Prime)) = ⊤ := by
  intro S
  have : Finite NativeSporadic.Fi24prime := ‹Finite (NativeSporadic.Carrier .Fi24Prime)›
  exact glbCore_two_eq_top_of_coreGenCheck (spec3 781) (D := CoreFi247.spec)
    (by show Nat.Prime 7; norm_num)
    (coreGenCheck_of_split _ _ _ _ _ _ CoreFi247.cutA CoreFi247.cutB
      Certificates.certificate9654 Certificates.certificate9655
      Certificates.certificate9656) S

end CFSG.AGLEmbeddingD2
