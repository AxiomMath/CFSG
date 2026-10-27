module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9591

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaMcL

theorem moduleDatum_McL_three :
    ModuleDatum NativeSporadic.McL 3 := by
  have hN : Nat.card NativeSporadic.McL = 898128000 := CFSG.Sporadic.McL.card_McL
  have : Finite NativeSporadic.McL := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheck (spec3 21) Nat.prime_three hN
    (by show 3 ^ 6 ∣ 898128000 ∧ ¬ 3 ^ 7 ∣ 898128000; norm_num)
    Certificates.certificate9591

theorem sporadicAlphaData_McL :
    SporadicAlphaData (NativeSporadic.Carrier .McL) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .McL)) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec4.card_outer_McL
  refine sporadicAlphaData_of_card CFSG.Sporadic.McL.card_McL (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 898128000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h, fun _ => Or.inr (Or.inr (Or.inl moduleDatum_McL_three)),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_McL⟩), fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
