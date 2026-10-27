module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import Certificates.Certificate9597

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaJ3

theorem moduleDatum_J3_three :
    ModuleDatum NativeSporadic.J3 3 := by
  have hN : Nat.card NativeSporadic.J3 = 50232960 := CFSG.Sporadic.J3.card_J3
  have : Finite NativeSporadic.J3 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckE (spec2 80) Nat.prime_three hN
    (by show 3 ^ 5 ∣ 50232960 ∧ ¬ 3 ^ 6 ∣ 50232960; norm_num)
    (by show 3 ^ 5 ≤ 9 * 3 ^ 3; norm_num)
    Certificates.certificate9597

theorem sporadicAlphaData_J3 :
    SporadicAlphaData (NativeSporadic.Carrier .J3) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .J3)) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec4.card_outer_J3
  refine sporadicAlphaData_of_card CFSG.Sporadic.J3.card_J3 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 50232960 = {2, 3, 5, 17, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_J3_three)),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
