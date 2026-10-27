module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9471

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem mcl_beta_fus3_check :
    fusCheck (ops3 21) NativeSporadic.McLSeed1 NativeSporadic.McLSeed2
      betaMcLP3N betaMcLP3Prog betaMcLP3 = true :=
  Certificates.certificate9471

theorem fusionGenerationOf_McL_three :
    FusionGenerationOf NativeSporadic.McL 3 :=
  fusionGenerationOf_of_check (spec3 21) (D := betaMcLP3) Nat.prime_three mcl_beta_fus3_check

theorem sporadicBetaData_McL :
    SporadicBetaData (NativeSporadic.Carrier .McL) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .McL)) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec4.card_outer_McL
  refine sporadicBetaData_of_card
    CFSG.Sporadic.McL.card_McL (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 898128000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_McL_three),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_McL⟩), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
