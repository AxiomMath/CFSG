module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicSmall
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Monster.B.TwoA.Fischer.M22Aut

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.Blueprint

theorem hasNoncommPair_three_M12 :
    HasNoncommPair 3 NativeSporadic.M12 := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem hasNoncommPair_three_M24 :
    HasNoncommPair 3 NativeSporadic.M24 := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem card_outer_M24 :
    Nat.card (Outer NativeSporadic.M24) = 1 := by
  change (inner NativeSporadic.M24).index = 1
  rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
    CFSG.Sporadic.Schreier.m24_mulAut_card, Subgroup.index_top]

section M11


theorem sporadicSmallData_M11 : SporadicSmallData (NativeSporadic.Carrier .M11) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.Mathieu.card_M11 (by norm_num)
    CFSG.Sporadic.Schreier.at_m11_schreier.1 ?_
  have hpf : Nat.primeFactors 7920 = {2, 3, 5, 11} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_M11 : SporadicBetaData (NativeSporadic.Carrier .M11) :=
  sporadicSmallData_M11.sporadicBetaData

theorem sporadicAlphaData_M11 : SporadicAlphaData (NativeSporadic.Carrier .M11) :=
  sporadicSmallData_M11.sporadicAlphaData

end M11

section M12


theorem sporadicSmallData_M12 : SporadicSmallData (NativeSporadic.Carrier .M12) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.Mathieu.card_M12 (by norm_num)
    CFSG.ComponentClassification.M12Cover.card_outer.le ?_
  have hpf : Nat.primeFactors 95040 = {2, 3, 5, 11} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr ⟨by norm_num, hasNoncommPair_three_M12⟩,
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_M12 : SporadicBetaData (NativeSporadic.Carrier .M12) :=
  sporadicSmallData_M12.sporadicBetaData

theorem sporadicAlphaData_M12 : SporadicAlphaData (NativeSporadic.Carrier .M12) :=
  sporadicSmallData_M12.sporadicAlphaData

end M12

section M22


theorem sporadicSmallData_M22 : SporadicSmallData (NativeSporadic.Carrier .M22) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.Mathieu.card_M22 (by norm_num)
    CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1.le ?_
  have hpf : Nat.primeFactors 443520 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_M22 : SporadicBetaData (NativeSporadic.Carrier .M22) :=
  sporadicSmallData_M22.sporadicBetaData

theorem sporadicAlphaData_M22 : SporadicAlphaData (NativeSporadic.Carrier .M22) :=
  sporadicSmallData_M22.sporadicAlphaData

end M22

section M23


theorem sporadicSmallData_M23 : SporadicSmallData (NativeSporadic.Carrier .M23) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.Schreier.m23_card (by norm_num)
    CFSG.Sporadic.Schreier.at_m23_schreier.1 ?_
  have hpf : Nat.primeFactors 10200960 = {2, 3, 5, 7, 11, 23} := by norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_M23 : SporadicBetaData (NativeSporadic.Carrier .M23) :=
  sporadicSmallData_M23.sporadicBetaData

theorem sporadicAlphaData_M23 : SporadicAlphaData (NativeSporadic.Carrier .M23) :=
  sporadicSmallData_M23.sporadicAlphaData

end M23

section M24


theorem sporadicSmallData_M24 : SporadicSmallData (NativeSporadic.Carrier .M24) := by
  refine sporadicSmallData_of_card CFSG.Sporadic.Mathieu.card_M24 (by norm_num)
    (card_outer_M24.trans_le (by norm_num)) ?_
  have hpf : Nat.primeFactors 244823040 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr ⟨by norm_num, hasNoncommPair_three_M24⟩,
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

theorem sporadicBetaData_M24 : SporadicBetaData (NativeSporadic.Carrier .M24) :=
  sporadicSmallData_M24.sporadicBetaData

theorem sporadicAlphaData_M24 : SporadicAlphaData (NativeSporadic.Carrier .M24) :=
  sporadicSmallData_M24.sporadicAlphaData

end M24

end CFSG.AGLEmbedding
