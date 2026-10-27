module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeThThree
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.AGLEmbedding.R3
open CFSG.Blueprint

theorem fusionGenerationOf_Th_three :
    FusionGenerationOf NativeSporadic.Th 3 := by
  have : Nontrivial NativeSporadic.Th :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [card_Th]; norm_num)
  exact fusionGenerationOf_of_tc Nat.prime_three tcGenDatum_Th_three

theorem sporadicBetaData_Th :
    SporadicBetaData (NativeSporadic.Carrier .Th) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Th)) ≤ 2 :=
    (CFSG.RankThree.PartOne.SPOR.card_outer_Th).le.trans (by norm_num)
  refine sporadicBetaData_of_card (n := 90745943887872000) card_Th (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Th_three),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Th⟩), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
