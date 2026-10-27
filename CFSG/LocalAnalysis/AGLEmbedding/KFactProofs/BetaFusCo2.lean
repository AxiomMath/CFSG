module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.Sporadic.Co2
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9474

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem co2_beta_fus3_check :
    fusCheck (ops2 22) NativeSporadic.Co2Seed1 NativeSporadic.Co2Seed2
      betaCo2P3N betaCo2P3Prog betaCo2P3 = true :=
  Certificates.certificate9474

theorem fusionGenerationOf_Co2_three :
    FusionGenerationOf NativeSporadic.Co2 3 :=
  fusionGenerationOf_of_check (spec2 22) (D := betaCo2P3) Nat.prime_three co2_beta_fus3_check

theorem sporadicBetaData_Co2 :
    SporadicBetaData (NativeSporadic.Carrier .Co2) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Co2)) ≤ 2 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_Co2.le.trans (by norm_num)
  refine sporadicBetaData_of_card
    CFSG.Sporadic.Co2.card_Co2 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 42305421312000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Co2_three),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Co2⟩), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
