module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.Sporadic.Co3
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9593

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo3

theorem moduleDatum_Co3_three :
    ModuleDatum NativeSporadic.Co3 3 := by
  have hN : Nat.card NativeSporadic.Co3 = 495766656000 := CFSG.Sporadic.Co3.card_Co3
  have : Finite NativeSporadic.Co3 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheck (spec2 22) Nat.prime_three hN
    (by show 3 ^ 7 ∣ 495766656000 ∧ ¬ 3 ^ 8 ∣ 495766656000; norm_num)
    Certificates.certificate9593

theorem sporadicAlphaData_Co3 :
    SporadicAlphaData (NativeSporadic.Carrier .Co3) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Co3)) ≤ 2 :=
    CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le.trans (by norm_num)
  refine sporadicAlphaData_of_card CFSG.Sporadic.Co3.card_Co3 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 495766656000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Co3_three)),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Co3⟩),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
