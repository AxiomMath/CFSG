module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9653

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.SectionRank CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.Open

theorem glbCore_J4_three [Finite (NativeSporadic.Carrier .J4)] :
    ∀ S : Sylow 3 (NativeSporadic.Carrier .J4),
      GLBCore 3 2 (S : Subgroup (NativeSporadic.Carrier .J4)) = ⊤ := by
  intro S
  have : Finite NativeSporadic.J4 := ‹Finite (NativeSporadic.Carrier .J4)›
  exact glbCore_two_eq_top_of_coreGenCheck (spec2 112) (D := CoreJ43.spec)
    (by show Nat.Prime 3; norm_num) Certificates.certificate9653 S

end CFSG.AGLEmbeddingD2
