module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.HN
public import CFSG.RankThree.PartOne.SPOR.Outer
public import Certificates.Certificate9480
public import Certificates.Certificate9481

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem hn_beta_fus3_check :
    fusCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2
      betaHNP3N betaHNP3Prog betaHNP3 = true :=
  Certificates.certificate9480

theorem fusionGenerationOf_HN_three :
    FusionGenerationOf NativeSporadic.HN 3 :=
  fusionGenerationOf_of_check (specP 5 133) (D := betaHNP3) Nat.prime_three hn_beta_fus3_check

theorem hn_beta_fus5_check :
    fusCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2
      betaHNP5N betaHNP5Prog betaHNP5 = true :=
  Certificates.certificate9481

theorem fusionGenerationOf_HN_five :
    FusionGenerationOf NativeSporadic.HN 5 :=
  fusionGenerationOf_of_check (specP 5 133) (D := betaHNP5) Nat.prime_five hn_beta_fus5_check

theorem sporadicBetaData_HN :
    SporadicBetaData (NativeSporadic.Carrier .HN) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .HN)) ≤ 2 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_HN.le
  refine sporadicBetaData_of_card
    CFSG.Sporadic.HN.card_HN (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 273030912000000 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_HN_three),
    fun _ => Or.inr (Or.inr fusionGenerationOf_HN_five), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
