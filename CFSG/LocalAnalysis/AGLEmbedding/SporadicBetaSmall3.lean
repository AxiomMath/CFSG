module

public import CFSG.Sporadic.Schreier.PairHSOut
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicSmall
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.Blueprint

theorem hasNoncommPair_three_He :
    HasNoncommPair 3 NativeSporadic.He := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem hasNoncommPair_three_Ru :
    HasNoncommPair 3 NativeSporadic.Ru := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

section HS


theorem sporadicSmallData_HS : SporadicSmallData (NativeSporadic.Carrier .HS) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.HS.card_HS (by norm_num)
    CFSG.Sporadic.Schreier.HS_outer_card_le_two.1 ?_
  have hpf : Nat.primeFactors 44352000 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inl (by norm_num),
    fun _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_HS⟩,
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_HS : SporadicBetaData (NativeSporadic.Carrier .HS) :=
  sporadicSmallData_HS.sporadicBetaData

theorem sporadicAlphaData_HS : SporadicAlphaData (NativeSporadic.Carrier .HS) :=
  sporadicSmallData_HS.sporadicAlphaData

end HS

section He


theorem sporadicSmallData_He : SporadicSmallData (NativeSporadic.Carrier .He) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.He.card_He (by norm_num)
    CFSG.Sporadic.Schreier.AT_He_Schreier.1 ?_
  have hpf : Nat.primeFactors 4030387200 = {2, 3, 5, 7, 17} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr ⟨by norm_num, hasNoncommPair_three_He⟩,
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_He⟩,
    fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_He : SporadicBetaData (NativeSporadic.Carrier .He) :=
  sporadicSmallData_He.sporadicBetaData

theorem sporadicAlphaData_He : SporadicAlphaData (NativeSporadic.Carrier .He) :=
  sporadicSmallData_He.sporadicAlphaData

end He

section Ru


theorem sporadicSmallData_Ru : SporadicSmallData (NativeSporadic.Carrier .Ru) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.Ru.card_Ru (by norm_num)
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      (CFSG.Sporadic.RuSchreier.card_outer_ruP.trans_le (by norm_num))
      CFSG.Sporadic.RuSchreier.ruEquivP) ?_
  have hpf : Nat.primeFactors 145926144000 = {2, 3, 5, 7, 13, 29} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr ⟨by norm_num, hasNoncommPair_three_Ru⟩,
    fun _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_Ru⟩,
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_Ru : SporadicBetaData (NativeSporadic.Carrier .Ru) :=
  sporadicSmallData_Ru.sporadicBetaData

theorem sporadicAlphaData_Ru : SporadicAlphaData (NativeSporadic.Carrier .Ru) :=
  sporadicSmallData_Ru.sporadicAlphaData

end Ru

end CFSG.AGLEmbedding
