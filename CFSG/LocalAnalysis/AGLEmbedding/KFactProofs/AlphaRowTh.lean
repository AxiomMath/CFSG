module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.SPOR.Outer

public import Certificates.Certificate9600

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaTh

theorem moduleDatum_Th_three :
    ModuleDatum NativeSporadic.Th 3 := by
  have hN : Nat.card NativeSporadic.Th = 90745943887872000 := card_Th
  have : Finite NativeSporadic.Th := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckW (spec2 248) Nat.prime_three hN
    (by show 3 ^ 10 ∣ 90745943887872000 ∧ ¬ 3 ^ 11 ∣ 90745943887872000; norm_num)
    Certificates.certificate9600

theorem sporadicAlphaData_Th :
    SporadicAlphaData (NativeSporadic.Carrier .Th) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Th)) ≤ 2 :=
    (CFSG.RankThree.PartOne.SPOR.card_outer_Th).le.trans (by norm_num)
  refine sporadicAlphaData_of_card card_Th (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Th_three)),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Th⟩),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
