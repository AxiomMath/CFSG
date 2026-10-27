module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import Certificates.Certificate9470

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem j3_beta_fus3_check :
    fusCheck (ops2 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2
      betaJ3P3N betaJ3P3Prog betaJ3P3 = true :=
  Certificates.certificate9470

theorem fusionGenerationOf_J3_three :
    FusionGenerationOf NativeSporadic.J3 3 :=
  fusionGenerationOf_of_check (spec2 80) (D := betaJ3P3) Nat.prime_three j3_beta_fus3_check

theorem sporadicBetaData_J3 :
    SporadicBetaData (NativeSporadic.Carrier .J3) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .J3)) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec4.card_outer_J3
  refine sporadicBetaData_of_card
    CFSG.Sporadic.J3.card_J3 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 50232960 = {2, 3, 5, 17, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_J3_three),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
