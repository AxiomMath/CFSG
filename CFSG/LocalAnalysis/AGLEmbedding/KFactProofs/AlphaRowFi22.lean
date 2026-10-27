module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22
public import Certificates.Certificate9595

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi22

theorem moduleDatum_Fi22_three :
    ModuleDatum NativeSporadic.Fi22 3 := by
  have hN : Nat.card NativeSporadic.Fi22 = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22
  have : Finite NativeSporadic.Fi22 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckE (spec3 77) Nat.prime_three hN
    (by show 3 ^ 9 ∣ 64561751654400 ∧ ¬ 3 ^ 10 ∣ 64561751654400; norm_num)
    (by show 3 ^ 9 ≤ 81 * 3 ^ 5; norm_num)
    Certificates.certificate9595

theorem sporadicAlphaData_Fi22 :
    SporadicAlphaData (NativeSporadic.Carrier .Fi22) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Fi22)) ≤ 2 :=
    CFSG.RankThree.PartOne.card_outer_fi22_carrier.le
  refine sporadicAlphaData_of_card CFSG.Sporadic.Fi22.card_Fi22 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 64561751654400 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Fi22_three)),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
