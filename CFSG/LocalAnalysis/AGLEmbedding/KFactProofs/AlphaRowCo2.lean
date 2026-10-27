module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.Sporadic.Co2
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9592

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo2

theorem moduleDatum_Co2_three :
    ModuleDatum NativeSporadic.Co2 3 := by
  have hN : Nat.card NativeSporadic.Co2 = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  have : Finite NativeSporadic.Co2 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheck (spec2 22) Nat.prime_three hN
    (by show 3 ^ 6 ∣ 42305421312000 ∧ ¬ 3 ^ 7 ∣ 42305421312000; norm_num)
    Certificates.certificate9592

theorem sporadicAlphaData_Co2 :
    SporadicAlphaData (NativeSporadic.Carrier .Co2) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Co2)) ≤ 2 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_Co2.le.trans (by norm_num)
  refine sporadicAlphaData_of_card CFSG.Sporadic.Co2.card_Co2 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 42305421312000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Co2_three)),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Co2⟩),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
