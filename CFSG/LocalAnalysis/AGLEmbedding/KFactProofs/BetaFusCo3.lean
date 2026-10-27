module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.Sporadic.Co3
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9473

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem co3_beta_fus3_check :
    fusCheck (ops2 22) NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2
      betaCo3P3N betaCo3P3Prog betaCo3P3 = true :=
  Certificates.certificate9473

theorem fusionGenerationOf_Co3_three :
    FusionGenerationOf NativeSporadic.Co3 3 :=
  fusionGenerationOf_of_check (spec2 22) (D := betaCo3P3) Nat.prime_three co3_beta_fus3_check

theorem sporadicBetaData_Co3 :
    SporadicBetaData (NativeSporadic.Carrier .Co3) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Co3)) ≤ 2 :=
    CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le.trans (by norm_num)
  refine sporadicBetaData_of_card
    CFSG.Sporadic.Co3.card_Co3 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 495766656000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Co3_three),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Co3⟩), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
