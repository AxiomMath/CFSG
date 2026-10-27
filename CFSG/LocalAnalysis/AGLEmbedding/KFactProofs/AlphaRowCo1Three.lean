module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Sporadic.Co1
public import Certificates.Certificate9596

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo1

theorem moduleDatum_Co1_three :
    ModuleDatum NativeSporadic.Co1 3 := by
  have hN : Nat.card NativeSporadic.Co1 = 4157776806543360000 := CFSG.Sporadic.Co1.card_Co1
  have : Finite NativeSporadic.Co1 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckE (spec2 24) Nat.prime_three hN
    (by show 3 ^ 9 ∣ 4157776806543360000 ∧ ¬ 3 ^ 10 ∣ 4157776806543360000; norm_num)
    (by show 3 ^ 9 ≤ 27 * 3 ^ 6; norm_num)
    Certificates.certificate9596

end CFSG.AGLEmbedding
