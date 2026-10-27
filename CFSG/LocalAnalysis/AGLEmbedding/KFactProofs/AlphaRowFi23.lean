module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import Certificates.Certificate9599

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi23

theorem moduleDatum_Fi23_three :
    ModuleDatum NativeSporadic.Fi23 3 := by
  have hN : Nat.card NativeSporadic.Fi23 = 4089470473293004800 := CFSG.Sporadic.Fi23.card_Fi23
  have : Finite NativeSporadic.Fi23 := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckW (spec3 253) Nat.prime_three hN
    (by show 3 ^ 13 ∣ 4089470473293004800 ∧ ¬ 3 ^ 14 ∣ 4089470473293004800; norm_num)
    Certificates.certificate9599

theorem sporadicAlphaData_Fi23 :
    SporadicAlphaData (NativeSporadic.Carrier .Fi23) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Fi23)) ≤ 2 :=
    CFSG.Sporadic.FischerOddCore.CTUC_Fi23_Schreier.1.le.trans (by norm_num)
  refine sporadicAlphaData_of_card CFSG.Sporadic.Fi23.card_Fi23 (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 4089470473293004800 = {2, 3, 5, 7, 11, 13, 17, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Fi23_three)),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
