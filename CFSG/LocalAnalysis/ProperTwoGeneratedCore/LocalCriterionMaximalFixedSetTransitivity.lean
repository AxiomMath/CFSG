module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def IsLocallyMaximalTwoPointPrime (H : Subgroup G) (p : ℕ)
    (P : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q →
    2 ≤ Nat.card (pointFixedSet H Q) → Q = P

@[expose] def IsMaximalTwoPointPrime (H : Subgroup G) (p : ℕ)
    (P : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q →
    2 ≤ Nat.card (pointFixedSet H Q) → Q = P

theorem locally_maximal_base_pair_flip [Finite G]
    {H P : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hP : IsPGroup p P) (hPH : P ≤ H)
    (hmax : IsLocallyMaximalTwoPointPrime H p P)
    (b : pointRightCosetSpace H) (hb : b ∈ pointFixedSet H P)
    (hbbase : b ≠ rightCosetMk H 1) :
    ∃ r ∈ involutionPointClass z,
      pointRightCosetMul H (rightCosetMk H 1) r = b ∧
      r ∈ Subgroup.normalizer (P : Set G) ∧
      Nat.card (conjugacyWithin P r) =
        p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  let B := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H b
  have hPB : P ≤ B := le_inf (by simpa only [rightCosetStabilizer_base] using hPH)
    ((mem_pointFixedSet_iff H P b).mp hb)
  have hPi : IsPGroup p (P.subgroupOf B) := hP.of_injective
    (Subgroup.subgroupOfEquivOfLe hPB).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hPB).injective
  obtain ⟨Q, hPQ⟩ := hPi.exists_le_sylow
  let QG := (Q : Subgroup B).map B.subtype
  have hPQG : P ≤ QG := by
    have hh := Subgroup.map_mono (f := B.subtype) hPQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hPB] at hh
  have hQGB : QG ≤ B := Subgroup.map_subtype_le _
  have hQGH : QG ≤ H := by
    have hh := hQGB.trans inf_le_left
    rwa [rightCosetStabilizer_base] at hh
  have haQ : rightCosetMk H 1 ∈ pointFixedSet H QG :=
    (mem_pointFixedSet_iff H QG _).mpr (hQGB.trans inf_le_left)
  have hbQ : b ∈ pointFixedSet H QG :=
    (mem_pointFixedSet_iff H QG _).mpr (hQGB.trans inf_le_right)
  have hQeq : QG = P := hmax QG hQGH (Q.isPGroup'.map B.subtype) hPQG
    (two_le_pointFixedSet_card_of_pair H QG _ b (Ne.symm hbbase) haQ hbQ)
  obtain ⟨r, hr, hra, _, hrnorm, hmotion⟩ := pair_specified_sylow_flip
    h T hzT hzcenter (rightCosetMk H 1) b (Ne.symm hbbase) p hp Q
  exact ⟨r, hr, hra, hQeq ▸ hrnorm, hQeq ▸ hmotion⟩

theorem locally_maximal_normalizer_transitive [Finite G]
    {H P : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hP : IsPGroup p P) (hPH : P ≤ H)
    (hmax : IsLocallyMaximalTwoPointPrime H p P) :
    ∀ a ∈ pointFixedSet H P, ∀ b ∈ pointFixedSet H P,
      ∃ n ∈ Subgroup.normalizer (P : Set G), pointRightCosetMul H a n = b := by
  have hbase (b : pointRightCosetSpace H) (hb : b ∈ pointFixedSet H P) :
      ∃ n ∈ Subgroup.normalizer (P : Set G),
        pointRightCosetMul H (rightCosetMk H 1) n = b := by
    by_cases heq : b = rightCosetMk H 1
    · exact ⟨1, Subgroup.one_mem _, by rw [pointRightCosetMul_one, heq]⟩
    obtain ⟨r, _, hrb, hrnorm, _⟩ := locally_maximal_base_pair_flip
      h T hzT hzcenter p hp hP hPH hmax b hb heq
    exact ⟨r, hrnorm, hrb⟩
  intro a ha b hb
  obtain ⟨na, hna, hnaa⟩ := hbase a ha
  obtain ⟨nb, hnb, hnbb⟩ := hbase b hb
  refine ⟨na⁻¹ * nb, (Subgroup.normalizer (P : Set G)).mul_mem
    ((Subgroup.normalizer (P : Set G)).inv_mem hna) hnb, ?_⟩
  rw [← hnaa, pointRightCosetMul_mul]
  simp only [mul_inv_cancel_left]
  exact hnbb

theorem locally_maximal_is_globally_maximal [Finite G]
    {H P : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hP : IsPGroup p P) (hPH : P ≤ H)
    (hmax : IsLocallyMaximalTwoPointPrime H p P) : IsMaximalTwoPointPrime H p P := by
  intro Q hQ hPQ hQfixed
  by_contra hne
  have hPstrict : P < Q := lt_of_le_of_ne hPQ (Ne.symm hne)
  let U := Q ⊓ Subgroup.normalizer (P : Set G)
  have hPU : P < U := pSubgroup_lt_normalizer_intersection p hp P Q hQ hPstrict
  have hU : IsPGroup p U := hQ.of_injective
    (Subgroup.inclusion (show U ≤ Q from inf_le_left)) (Subgroup.inclusion_injective _)
  have hUfixed : 2 ≤ Nat.card (pointFixedSet H U) := hQfixed.trans
    (Set.ncard_le_ncard (pointFixedSet_antitone (show U ≤ Q from inf_le_left)))
  have hnonzero : Nat.card (pointFixedSet H U) ≠ 0 := by omega
  have : Nonempty (pointFixedSet H U) := (Nat.card_ne_zero.mp hnonzero).1
  obtain ⟨a, ha⟩ := this
  have haP := pointFixedSet_antitone hPU.le ha
  have hbaseP : rightCosetMk H 1 ∈ pointFixedSet H P := by
    apply (mem_pointFixedSet_iff H P _).mpr
    rwa [rightCosetStabilizer_base]
  obtain ⟨n, hn, hna⟩ := locally_maximal_normalizer_transitive
    h T hzT hzcenter p hp hP hPH hmax a haP (rightCosetMk H 1) hbaseP
  have hUconj : IsPGroup p (rightConjugate U n) := hU.map (MulAut.conj n⁻¹).toMonoidHom
  have hUnH : rightConjugate U n ≤ H := by
    have hafixed := pointFixedSet_rightConjugate_mem H U n ha
    rw [hna] at hafixed
    simpa only [rightCosetStabilizer_base] using
      (mem_pointFixedSet_iff H (rightConjugate U n) _).mp hafixed
  have hPconj : rightConjugate P n = P := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (P : Set G)).inv_mem hn)
  have hstrict : P < rightConjugate U n := by
    have hh := (Subgroup.map_lt_map_iff_of_injective
      (f := (MulAut.conj n⁻¹).toMonoidHom) (MulAut.conj n⁻¹).injective).mpr hPU
    change rightConjugate P n < rightConjugate U n at hh
    rwa [hPconj] at hh
  have hUnfixed : 2 ≤ Nat.card (pointFixedSet H (rightConjugate U n)) := by
    simpa only [pointFixedSet_rightConjugate_card] using hUfixed
  exact (ne_of_gt hstrict) (hmax _ hUnH hUconj hstrict.le hUnfixed)

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
