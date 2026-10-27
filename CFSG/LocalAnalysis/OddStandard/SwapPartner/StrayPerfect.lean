module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma39

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

theorem four_dvd_card_of_isPerfect {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    [Nontrivial J] : 4 ∣ Nat.card J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : Even (Nat.card J) := by
    rw [← Nat.not_odd_iff_even]
    intro hodd
    exact Group.IsPerfect.not_isSolvable J (CFSG.Milestones.odd_order_solvable hodd)
  let S : Sylow 2 J := Classical.choice Sylow.nonempty
  have hSnotcyc : ¬ IsCyclic ↥(S : Subgroup J) :=
    CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_perfect J heven S
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_le h)
    refine hSnotcyc (isCyclic_of_card_dvd_prime (p := 2) ?_)
    rw [show Nat.card (S : Subgroup J) = 2 ^ k from hk]
    simpa using pow_dvd_pow 2 hk1
  have h4S : 4 ∣ Nat.card (S : Subgroup J) := by
    rw [show Nat.card (S : Subgroup J) = 2 ^ k from hk]
    exact dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (pow_dvd_pow 2 hk2)
  exact h4S.trans (Subgroup.card_subgroup_dvd_card (S : Subgroup J))

theorem card_sup_zpowers_eq_two_mul {X : Type*} [Group X] [Finite X] {J : Subgroup X} {t : X}
    (ht2 : t ^ 2 = 1) (htN : t ∈ normalizer (J : Set X)) (htJ : t ∉ J) :
    Nat.card ↥(J ⊔ zpowers t) = 2 * Nat.card J := by
  have h2 : t * t = 1 := by rw [← pow_two]; exact ht2
  have htinj : t⁻¹ = t := inv_eq_of_mul_eq_one_right h2
  have htM : t ∈ J ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hrel : J.relIndex (J ⊔ zpowers t) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, htM, fun b hb => ?_⟩
    have hb' : b ∈ zpowers t ⊔ J := by rwa [sup_comm] at hb
    rcases CFSG.ComponentClassification.AschbacherKnownGroup.Lemma39.mem_zpowers_sup ht2 htN hb'
      with hbJ | ⟨y, hy, hb_eq⟩
    · refine Or.inr ⟨hbJ, fun hbt => ?_⟩
      apply htJ
      have hmul : b⁻¹ * (b * t) = t := by group
      rw [← hmul]
      exact J.mul_mem (J.inv_mem hbJ) hbt
    · rw [hb_eq]
      refine Or.inl ⟨?_, fun hbJ => ?_⟩
      · have hconj : t * y * t⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 htN y).1 hy
        rwa [htinj] at hconj
      · apply htJ
        have hmul : (t * y) * y⁻¹ = t := by group
        rw [← hmul]
        exact J.mul_mem hbJ (J.inv_mem hy)
  have hcard := Subgroup.relIndex_mul_card (H := J) (K := J ⊔ zpowers t)
  rw [inf_of_le_left le_sup_left, hrel] at hcard
  exact hcard.symm

end CFSG.OddStandard.AltStdSec.SwapPartner
