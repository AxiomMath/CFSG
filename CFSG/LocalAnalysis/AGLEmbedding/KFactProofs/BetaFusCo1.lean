module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Sporadic.Co1
public import CFSG.RankThree.PartOne.SPOR.Outer
public import Certificates.Certificate9476
public import Certificates.Certificate9477

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem co1_beta_fus3_check :
    fusCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2
      betaCo1P3N betaCo1P3Prog betaCo1P3 = true :=
  Certificates.certificate9476

theorem fusionGenerationOf_Co1_three :
    FusionGenerationOf NativeSporadic.Co1 3 :=
  fusionGenerationOf_of_check (spec2 24) (D := betaCo1P3) Nat.prime_three co1_beta_fus3_check

theorem co1_beta_fus5_check :
    fusCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2
      betaCo1P5N betaCo1P5Prog betaCo1P5 = true :=
  Certificates.certificate9477

theorem fusionGenerationOf_Co1_five :
    FusionGenerationOf NativeSporadic.Co1 5 :=
  fusionGenerationOf_of_check (spec2 24) (D := betaCo1P5) Nat.prime_five co1_beta_fus5_check

theorem sporadicBetaData_Co1 :
    SporadicBetaData (NativeSporadic.Carrier .Co1) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Co1)) ≤ 2 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_Co1.le.trans (by norm_num)
  refine sporadicBetaData_of_card
    CFSG.Sporadic.Co1.card_Co1 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 4157776806543360000 = {2, 3, 5, 7, 11, 13, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Co1_three),
    fun _ => Or.inr (Or.inr fusionGenerationOf_Co1_five), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
