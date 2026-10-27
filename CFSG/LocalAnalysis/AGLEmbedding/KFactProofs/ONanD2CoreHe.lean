module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate9512
public import Certificates.Certificate9513

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.SectionRank CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.Open

theorem glbCore_He_three [Finite (NativeSporadic.Carrier .He)] :
    ∀ S : Sylow 3 (NativeSporadic.Carrier .He),
      GLBCore 3 2 (S : Subgroup (NativeSporadic.Carrier .He)) = ⊤ := by
  intro S
  have : Finite NativeSporadic.He := ‹Finite (NativeSporadic.Carrier .He)›
  exact glbCore_two_eq_top_of_coreGenCheck (specP 7 50) (D := CoreHe3.spec)
    (by show Nat.Prime 3; norm_num) Certificates.certificate9512 S

theorem glbCore_He_seven [Finite (NativeSporadic.Carrier .He)] :
    ∀ S : Sylow 7 (NativeSporadic.Carrier .He),
      GLBCore 7 2 (S : Subgroup (NativeSporadic.Carrier .He)) = ⊤ := by
  intro S
  have : Finite NativeSporadic.He := ‹Finite (NativeSporadic.Carrier .He)›
  exact glbCore_two_eq_top_of_coreGenCheck (specP 7 50) (D := CoreHe7.spec)
    (by show Nat.Prime 7; norm_num)
    Certificates.certificate9513 S

end CFSG.AGLEmbeddingD2
