module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MatOpsChecks
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.RankThree.PartOne.CTP.SporadicNoncommFi24
public import Certificates.Certificate9602

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi24

theorem moduleDatum_Fi24_three :
    ModuleDatum NativeSporadic.Fi24prime 3 := by
  have hN : Nat.card NativeSporadic.Fi24prime = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have : Finite NativeSporadic.Fi24prime := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  exact moduleDatum_of_modCheckV (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) Nat.prime_three hN
    (by show 3 ^ 16 ∣ 1255205709190661721292800 ∧ ¬ 3 ^ 17 ∣ 1255205709190661721292800; norm_num)
    (modCheckV_matOps Certificates.certificate9602)

theorem sporadicAlphaData_Fi24 :
    SporadicAlphaData (NativeSporadic.Carrier .Fi24Prime) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .Fi24Prime)) ≤ 2 :=
    CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime.le
  refine sporadicAlphaData_of_card CFSG.Sporadic.Fi24.card_Fi24prime (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 1255205709190661721292800 = {2, 3, 5, 7, 11, 13, 17, 23, 29} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inl moduleDatum_Fi24_three)),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_Fi24_seven⟩),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num),
    fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
