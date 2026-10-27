module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import Certificates.Certificate9484

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem fi23_beta_fus3_check :
    fusCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2
      betaFi23P3N betaFi23P3Prog betaFi23P3 = true :=
  Certificates.certificate9484

theorem fusionGenerationOf_Fi23_three :
    FusionGenerationOf NativeSporadic.Fi23 3 :=
  fusionGenerationOf_of_check (spec3 253) (D := betaFi23P3) Nat.prime_three fi23_beta_fus3_check

theorem sporadicBetaData_Fi23 :
    SporadicBetaData (NativeSporadic.Carrier .Fi23) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Fi23)) ≤ 2 :=
    CFSG.Sporadic.FischerOddCore.CTUC_Fi23_Schreier.1.le.trans (by norm_num)
  refine sporadicBetaData_of_card
    CFSG.Sporadic.Fi23.card_Fi23 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 4089470473293004800 = {2, 3, 5, 7, 11, 13, 17, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Fi23_three),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
