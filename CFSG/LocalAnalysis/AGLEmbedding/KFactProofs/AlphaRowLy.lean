module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowLyThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowLyFive
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem sporadicAlphaData_Ly :
    SporadicAlphaData (NativeSporadic.Carrier .Ly) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Ly)) ≤ 2 := by
    rcases CFSG.RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> omega
  refine sporadicAlphaData_of_card CFSG.Sporadic.Ly.card_Ly' (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 51765179004000000 = {2, 3, 5, 7, 11, 31, 37, 67} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Ly_three)),
    fun _ => Or.inr (Or.inr (Or.inr (Or.inr rankLiftDatum_Ly_five))),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
