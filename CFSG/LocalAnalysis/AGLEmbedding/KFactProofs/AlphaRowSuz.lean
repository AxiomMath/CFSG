module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.SuzOddCore.Outer
public import Certificates.Certificate9594

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaSuz

theorem moduleDatum_Suz_three :
    ModuleDatum NativeSporadic.Suz 3 := by
  have hN : Nat.card NativeSporadic.Suz = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  have : Finite NativeSporadic.Suz := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckE (spec3 64) Nat.prime_three hN
    (by show 3 ^ 7 ∣ 448345497600 ∧ ¬ 3 ^ 8 ∣ 448345497600; norm_num)
    (by show 3 ^ 7 ≤ 9 * 3 ^ 5; norm_num)
    Certificates.certificate9594

theorem sporadicAlphaData_Suz :
    SporadicAlphaData (NativeSporadic.Carrier .Suz) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Suz)) ≤ 2 :=
    CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1.le
  refine sporadicAlphaData_of_card CFSG.Sporadic.Suz.card_Suz (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 448345497600 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Suz_three)),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
