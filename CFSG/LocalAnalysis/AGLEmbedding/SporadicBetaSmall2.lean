module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicSmall
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.Blueprint

theorem hasNoncommPair_three_J2 :
    HasNoncommPair 3 NativeSporadic.J2 := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem hasNoncommPair_three_J4 :
    HasNoncommPair 3 NativeSporadic.J4 := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem card_outer_J4 :
    Nat.card (Outer (NativeSporadic.Carrier .J4)) = 1 := by
  have hodd := CFSG.Sporadic.J4Schreier.outer_carrier_J4_odd
  have h3 := CFSG.RankThree.PartTwo.Sec4.inputs47Core_outJ4
  have hT : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
  have h23 := (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes hT).1
  by_contra hne
  have hd := Nat.minFac_dvd (Nat.card (Outer (NativeSporadic.Carrier .J4)))
  rcases h23 _ (Nat.minFac_prime hne) hd with h | h <;> rw [h] at hd
  · exact Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 hd)
  · exact h3 hd

section J1


theorem sporadicSmallData_J1 : SporadicSmallData (NativeSporadic.Carrier .J1) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.J1.card_J1 (by norm_num)
    (CFSG.Sporadic.Schreier.at_j1_schreier.1.trans_le (by norm_num)) ?_
  have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_J1 : SporadicBetaData (NativeSporadic.Carrier .J1) :=
  sporadicSmallData_J1.sporadicBetaData

theorem sporadicAlphaData_J1 : SporadicAlphaData (NativeSporadic.Carrier .J1) :=
  sporadicSmallData_J1.sporadicAlphaData

end J1

section J2


theorem sporadicSmallData_J2 : SporadicSmallData (NativeSporadic.Carrier .J2) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.J2.card_J2 (by norm_num)
    CFSG.Sporadic.Schreier.AT_J2_Schreier.1 ?_
  have hpf : Nat.primeFactors 604800 = {2, 3, 5, 7} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr ⟨by norm_num, hasNoncommPair_three_J2⟩,
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_J2 : SporadicBetaData (NativeSporadic.Carrier .J2) :=
  sporadicSmallData_J2.sporadicBetaData

theorem sporadicAlphaData_J2 : SporadicAlphaData (NativeSporadic.Carrier .J2) :=
  sporadicSmallData_J2.sporadicAlphaData

end J2

section J4


theorem sporadicSmallData_J4 : SporadicSmallData (NativeSporadic.Carrier .J4) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.J4.card_J4 (by norm_num)
    (card_outer_J4.trans_le (by norm_num)) ?_
  have hpf : Nat.primeFactors 86775571046077562880 = {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr ⟨by norm_num, hasNoncommPair_three_J4⟩,
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_J4⟩,
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_J4 : SporadicBetaData (NativeSporadic.Carrier .J4) :=
  sporadicSmallData_J4.sporadicBetaData

theorem sporadicAlphaData_J4 : SporadicAlphaData (NativeSporadic.Carrier .J4) :=
  sporadicSmallData_J4.sporadicAlphaData

end J4

end CFSG.AGLEmbedding
