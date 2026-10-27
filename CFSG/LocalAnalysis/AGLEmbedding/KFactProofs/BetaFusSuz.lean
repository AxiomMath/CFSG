module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.SuzOddCore.Outer
public import Certificates.Certificate9472

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem suz_beta_fus3_check :
    fusCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2
      betaSuzP3N betaSuzP3Prog betaSuzP3 = true :=
  Certificates.certificate9472

theorem fusionGenerationOf_Suz_three :
    FusionGenerationOf NativeSporadic.Suz 3 :=
  fusionGenerationOf_of_check (spec3 64) (D := betaSuzP3) Nat.prime_three suz_beta_fus3_check

theorem sporadicBetaData_Suz :
    SporadicBetaData (NativeSporadic.Carrier .Suz) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Suz)) ≤ 2 :=
    CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1.le
  refine sporadicBetaData_of_card
    CFSG.Sporadic.Suz.card_Suz (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 448345497600 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Suz_three),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
