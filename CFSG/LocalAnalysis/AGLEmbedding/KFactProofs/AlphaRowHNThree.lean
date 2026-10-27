module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.HN
public import Certificates.Certificate9598

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHN

theorem moduleDatum_HN_three :
    ModuleDatum NativeSporadic.HN 3 := by
  have hN : Nat.card NativeSporadic.HN = 273030912000000 := CFSG.Sporadic.HN.card_HN
  have : Finite NativeSporadic.HN := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckE (specP 5 133) Nat.prime_three hN
    (by show 3 ^ 6 ∣ 273030912000000 ∧ ¬ 3 ^ 7 ∣ 273030912000000; norm_num)
    (by show 3 ^ 6 ≤ 9 * 3 ^ 4; norm_num)
    Certificates.certificate9598

end CFSG.AGLEmbedding
