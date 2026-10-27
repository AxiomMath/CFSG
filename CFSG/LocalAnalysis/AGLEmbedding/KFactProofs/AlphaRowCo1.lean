module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo1Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo1Five
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem sporadicAlphaData_Co1 :
    SporadicAlphaData (NativeSporadic.Carrier .Co1) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Co1)) ≤ 2 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_Co1.le.trans (by norm_num)
  refine sporadicAlphaData_of_card CFSG.Sporadic.Co1.card_Co1 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 4157776806543360000 = {2, 3, 5, 7, 11, 13, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Co1_three)),
    fun _ => Or.inr (Or.inr (Or.inr (Or.inr rankLiftDatum_Co1_five))),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
