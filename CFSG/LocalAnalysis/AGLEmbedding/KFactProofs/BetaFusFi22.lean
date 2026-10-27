module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22
public import Certificates.Certificate9478

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem fi22_beta_fus3_check :
    fusCheck (ops3 77) NativeSporadic.Fi22Seed1 NativeSporadic.Fi22Seed2
      betaFi22P3N betaFi22P3Prog betaFi22P3 = true :=
  Certificates.certificate9478

theorem fusionGenerationOf_Fi22_three :
    FusionGenerationOf NativeSporadic.Fi22 3 :=
  fusionGenerationOf_of_check (spec3 77) (D := betaFi22P3) Nat.prime_three fi22_beta_fus3_check

theorem sporadicBetaData_Fi22 :
    SporadicBetaData (NativeSporadic.Carrier .Fi22) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Fi22)) ≤ 2 :=
    CFSG.RankThree.PartOne.card_outer_fi22_carrier.le
  refine sporadicBetaData_of_card
    CFSG.Sporadic.Fi22.card_Fi22 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 64561751654400 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Fi22_three),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
