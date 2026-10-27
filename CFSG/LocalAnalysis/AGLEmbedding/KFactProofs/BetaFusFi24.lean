module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.RankThree.PartOne.CTP.SporadicNoncommFi24
public import Certificates.Certificate9485

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem fi24_beta_fus3_check :
    fusCheck (ops3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2
      betaFi24P3N betaFi24P3Prog betaFi24P3 = true :=
  Certificates.certificate9485

theorem fusionGenerationOf_Fi24_three :
    FusionGenerationOf NativeSporadic.Fi24prime 3 :=
  fusionGenerationOf_of_check (spec3 781) (D := betaFi24P3) Nat.prime_three fi24_beta_fus3_check

theorem sporadicBetaData_Fi24Prime :
    SporadicBetaData (NativeSporadic.Carrier .Fi24Prime) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Fi24Prime)) ≤ 2 :=
    CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime.le
  refine sporadicBetaData_of_card
    CFSG.Sporadic.Fi24.card_Fi24prime (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 1255205709190661721292800 = {2, 3, 5, 7, 11, 13, 17, 23, 29} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Fi24_three),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Fi24_seven⟩),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
