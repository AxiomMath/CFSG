module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.Ly.Primitive
public import Certificates.Certificate9601

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaLy

theorem moduleDatum_Ly_three :
    ModuleDatum NativeSporadic.Ly 3 := by
  have hN : Nat.card NativeSporadic.Ly = 51765179004000000 := CFSG.Sporadic.Ly.card_Ly'
  have : Finite NativeSporadic.Ly := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckW (specP 5 111) Nat.prime_three hN
    (by show 3 ^ 7 ∣ 51765179004000000 ∧ ¬ 3 ^ 8 ∣ 51765179004000000; norm_num)
    Certificates.certificate9601

end CFSG.AGLEmbedding
