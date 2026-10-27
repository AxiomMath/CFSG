module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowHNThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowHNFive
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem sporadicAlphaData_HN :
    SporadicAlphaData (NativeSporadic.Carrier .HN) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .HN)) ≤ 2 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_HN.le
  refine sporadicAlphaData_of_card CFSG.Sporadic.HN.card_HN (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 273030912000000 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_HN_three)),
    fun _ => Or.inr (Or.inr (Or.inr (Or.inr rankLiftDatum_HN_five))),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
