module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberCount
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma sq_eq_one_of_isConj_orderOf_two {G : Type*} [Group G] {z t : G}
    (hz : orderOf z = 2) (ht : IsConj z t) : t ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 ht
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  calc t ^ 2 = (c * z * c⁻¹) ^ 2 := by rw [hc]
    _ = c * z ^ 2 * c⁻¹ := conj_pow
    _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]

theorem gzNo_mem_Qz_symm {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hOrb : Vert GzOrbitFacts a z) {t v : G} (ht : IsConj z t) (hv : IsConj z v)
    (hvt : v ∈ Qz t) : t ∈ Qz v := by
  by_cases htv : v = t
  · subst htv
    exact self_mem_Qz (sq_eq_one_of_isConj_orderOf_two h.orderOf_z ht)
  · by_contra hnot
    have hv' : IsF5Type a v := isF5Type_of_isConj h (IsConj.refl a) hv
    have hOt : GzOrbitFacts a t := hOrb a t (IsConj.refl a) ht
    have hQz_le : Qz t ≤ Gx t := Subgroup.map_subtype_le _
    have hvt_Gx : v ∈ Gx t := hQz_le hvt
    have ht_Gx_v : t ∈ Gx v := mem_Gx.mpr (mem_Gx.mp hvt_Gx).symm
    let C := ↥(Gx v)
    let Q : Subgroup C := CFSG.pCore 2 C
    haveI hQn : Q.Normal := CFSG.pCore_normal
    have hQ : IsExtraspecialPlusByA5WrTwoWith C Q :=
      isExtraspecialPlusByA5WrTwoWith_pCore hv'.cent_z
    let c : C := ⟨t, ht_Gx_v⟩
    obtain ⟨e⟩ := nonempty_mulEquiv_Gbar hv'
    have hQcard : Nat.card ↥Q = 512 := by
      obtain ⟨-, hcard, -⟩ := hQ.plus
      norm_num at hcard
      exact hcard
    have hc_card : Nat.card ↥(Subgroup.centralizer ({c} : Set C)) = 2 ^ 13 * 3 := by
      change Nat.card ↥(Subgroup.centralizer
        ({(⟨t, ht_Gx_v⟩ : ↥(Gx v))} : Set ↥(Gx v))) = 2 ^ 13 * 3
      rw [← card_Gx_inf_eq (z := v) (c := t) ht_Gx_v, inf_comm]
      exact hOt.orbit_QB.2 v ⟨hvt, ht.symm.trans hv, htv⟩
    have ht2 : t ^ 2 = 1 := sq_eq_one_of_isConj_orderOf_two h.orderOf_z ht
    have hc2 : c ^ 2 = 1 := by
      apply Subtype.ext
      change ((c : C) : G) ^ 2 = 1
      exact ht2
    have hbar_ne_one : barOf v c ≠ 1 := by
      intro h1
      exact hnot ((barOf_eq_one_iff c).mp h1)
    have hbar2 : (barOf v c) ^ 2 = 1 := by
      show ((c : C ⧸ Q)) ^ 2 = 1
      rw [← QuotientGroup.mk_pow, hc2, QuotientGroup.mk_one]
    set Fc : ℕ := Nat.card {s : C // (∃ k : C, k * c * k⁻¹ = s) ∧
      (s : C ⧸ Q) = (c : C ⧸ Q)} with hFc
    set n : ℕ := Nat.card ↥(Subgroup.centralizer ({(c : C ⧸ Q)} : Set (C ⧸ Q))) with hn
    have hmain : Fc * 24576 = 512 * n := by
      rw [hFc, hn]
      have h := card_fiber_mul_card_centralizer Q c
      rw [hc_card, hQcard] at h
      norm_num at h
      exact h
    have hn_cases : n = 120 ∨ n = 240 ∨ n = 32 := by
      rw [hn]
      rcases involution_cases_of_mulEquiv e hbar2 hbar_ne_one with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · left; simpa using h
      · right; left; simpa using h
      · right; right; simpa using h
    have hFc5 : Fc = 5 := by
      rcases hn_cases with h | h | h
      · rw [h] at hmain; omega
      · rw [h] at hmain; omega
      · rw [h] at hmain; omega
    set m : ℕ := Nat.card ↥(Subgroup.centralizer ({c} : Set C) ⊓ Q) with hm
    have hdiv : 512 ∣ 5 * m := by
      have h := card_dvd_card_fiber_mul Q c
      rw [hQcard] at h
      rw [← hFc, hFc5, ← hm] at h
      exact h
    have hm_le : m ≤ 512 := by
      rw [hm]
      calc Nat.card ↥(Subgroup.centralizer ({c} : Set C) ⊓ Q) ≤ Nat.card ↥Q :=
            Subgroup.card_le_of_le inf_le_right
        _ = 512 := hQcard
    have hm_pos : 1 ≤ m := by
      rw [hm]
      exact Nat.card_pos
    have hm_eq : m = 512 := by
      obtain ⟨k, hk⟩ := hdiv
      omega
    have hinf_eq : Subgroup.centralizer ({c} : Set C) ⊓ Q = Q := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      rw [← hm, hm_eq, hQcard]
    have hc_cent : c ∈ Subgroup.centralizer (Q : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq_inf : q ∈ Subgroup.centralizer ({c} : Set C) ⊓ Q := by
        rw [hinf_eq]; exact hq
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hq_inf).1
    have hcQ : c ∈ Q := hQ.centralizer_le hc_cent
    have htQz : t ∈ Qz v := by
      have h := Subgroup.mem_map_of_mem (Gx v).subtype hcQ
      exact h
    exact hnot htQz

end CFSG.EvenSporadicStandard.HNRecog.Section3
