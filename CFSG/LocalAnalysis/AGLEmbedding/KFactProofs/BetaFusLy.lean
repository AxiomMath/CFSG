module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeLyThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeLyFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeTc
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.AGLEmbedding.R3
open CFSG.Blueprint

theorem fusionGenerationOf_Ly_three :
    FusionGenerationOf NativeSporadic.Ly 3 := by
  have : Nontrivial NativeSporadic.Ly :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [CFSG.Sporadic.Ly.card_Ly']; norm_num)
  exact fusionGenerationOf_of_tc Nat.prime_three tcGenDatum_Ly_three

theorem fusionGenerationOf_Ly_five :
    FusionGenerationOf NativeSporadic.Ly 5 := by
  have : Nontrivial NativeSporadic.Ly :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [CFSG.Sporadic.Ly.card_Ly']; norm_num)
  exact fusionGenerationOf_of_tc Nat.prime_five tcGenDatum_Ly_five

theorem sporadicBetaData_Ly :
    SporadicBetaData (NativeSporadic.Carrier .Ly) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Ly)) ≤ 2 := by
    rcases CFSG.RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> omega
  refine sporadicBetaData_of_card (n := 51765179004000000) CFSG.Sporadic.Ly.card_Ly'
    (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 51765179004000000 = {2, 3, 5, 7, 11, 31, 37, 67} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr fusionGenerationOf_Ly_three),
    fun _ => Or.inr (Or.inr fusionGenerationOf_Ly_five), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
