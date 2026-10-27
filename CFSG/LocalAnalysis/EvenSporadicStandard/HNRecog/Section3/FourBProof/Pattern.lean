module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.InvGa
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {G : Type} [Group G] {a z p q : G}

private theorem fourB_ne_one_of_orderOf {t : G} (ht2 : orderOf t = 2) : t ≠ 1 := by
  intro h
  rw [h, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

private theorem fourB_sq_of_orderOf {t : G} (ht2 : orderOf t = 2) : t ^ 2 = 1 := by
  have h := pow_orderOf_eq_one t
  rwa [ht2] at h

private theorem fourB_mul_self_of_orderOf {t : G} (ht2 : orderOf t = 2) : t * t = 1 := by
  simpa [pow_two] using fourB_sq_of_orderOf ht2

theorem fourB_cls_t (H : FourBHyps a z) (P : FourBPair a p q) {t : G} (ht : t ∈ Gxy p q)
    (ht2 : orderOf t = 2) : IsConj a t ∨ IsConj z t := by
  obtain ⟨htp, -⟩ := mem_Gxy.mp ht
  have hpt : p * t = t * p := mem_Gx.mp htp
  exact isConj_of_commute H.hF1 H.hF2 P.hp hpt.symm
    (fourB_sq_of_orderOf ht2) (fourB_ne_one_of_orderOf ht2)

theorem fourB_cls_pt (H : FourBHyps a z) (P : FourBPair a p q) {t : G} (ht : t ∈ Gxy p q)
    (ht2 : orderOf t = 2) : IsConj a (p * t) ∨ IsConj z (p * t) := by
  obtain ⟨htp, htq⟩ := mem_Gxy.mp ht
  have hpt : p * t = t * p := mem_Gx.mp htp
  have hqt : q * t = t * q := mem_Gx.mp htq
  have htp_ne : t ≠ p := by
    intro h
    have h' := hqt
    rw [h] at h'
    exact fourB_pq_ne H P h'.symm
  have hcomm : (p * t) * p = p * (p * t) := by rw [mul_assoc, ← hpt]
  have hord : orderOf (p * t) = 2 :=
    fourB_orderOf_mul_of_comm (fourB_orderOf_p H P) ht2 hpt (fun h => htp_ne h.symm)
  exact isConj_of_commute H.hF1 H.hF2 P.hp hcomm
    (fourB_sq_of_orderOf hord) (fourB_ne_one_of_orderOf hord)

theorem fourB_cls_qt (H : FourBHyps a z) (P : FourBPair a p q) {t : G} (ht : t ∈ Gxy p q)
    (ht2 : orderOf t = 2) : IsConj a (q * t) ∨ IsConj z (q * t) := by
  obtain ⟨htp, htq⟩ := mem_Gxy.mp ht
  have hpt : p * t = t * p := mem_Gx.mp htp
  have hqt : q * t = t * q := mem_Gx.mp htq
  have htq_ne : t ≠ q := by
    intro h
    have h' := hpt
    rw [h] at h'
    exact fourB_pq_ne H P h'
  have hcomm : (q * t) * q = q * (q * t) := by rw [mul_assoc, ← hqt]
  have hord : orderOf (q * t) = 2 :=
    fourB_orderOf_mul_of_comm (fourB_orderOf_q H P) ht2 hqt (fun h => htq_ne h.symm)
  exact isConj_of_commute H.hF1 H.hF2 P.hq hcomm
    (fourB_sq_of_orderOf hord) (fourB_ne_one_of_orderOf hord)

theorem fourB_no_BAA (H : FourBHyps a z) (P : FourBPair a p q) {t : G} (ht : t ∈ Gxy p q)
    (ht2 : orderOf t = 2) : ¬ (IsConj z t ∧ IsConj a (p * t) ∧ IsConj a (q * t)) := by
  rintro ⟨hzt, hptA, hqtA⟩
  obtain ⟨htp, htq⟩ := mem_Gxy.mp ht
  have hpt : p * t = t * p := mem_Gx.mp htp
  have hqt : q * t = t * q := mem_Gx.mp htq
  have hpQ : p ∈ Qz t := mem_Qz_of_isConj_mul H.hI H.h H.hF1 P.hp hzt hpt hptA
  have hqQ : q ∈ Qz t := mem_Qz_of_isConj_mul H.hI H.h H.hF1 P.hq hzt hqt hqtA
  have hF5t : IsF5Type a t := isF5Type_of_isConj H.h (IsConj.refl a) hzt
  have hmem : ⁅p, q⁆ ∈ Subgroup.zpowers t :=
    commutatorElement_mem_zpowers_of_mem_Qz hF5t hpQ hqQ
  have hp2 : p * p = 1 := fourB_mul_self_of_orderOf (fourB_orderOf_p H P)
  have hq2 : q * q = 1 := fourB_mul_self_of_orderOf (fourB_orderOf_q H P)
  have hcomm_eq : ⁅p, q⁆ = (p * q) ^ 2 := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hp2,
      inv_eq_of_mul_eq_one_right hq2, pow_two]
    group
  rw [hcomm_eq] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hb1 : (p * q) ^ 2 ≠ 1 := by
    intro h
    have hb2 := fourB_orderOf_b H P
    rw [h, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  have ht2' : t ^ 2 = 1 := fourB_sq_of_orderOf ht2
  have ht2z : t ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, ht2']
  have hb_eq_t : (p * q) ^ 2 = t := by
    rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
    · rw [hm] at hk
      have hzero : t ^ (2 * m) = 1 := by rw [zpow_mul, ht2z, one_zpow]
      rw [hzero] at hk
      exact absurd hk.symm hb1
    · rw [hm] at hk
      have hodd : t ^ (2 * m + 1) = t := by
        rw [zpow_add, zpow_mul, ht2z, one_zpow, one_mul, zpow_one]
      rw [hodd] at hk
      exact hk.symm
  have hAt : IsConj a t := by
    have h' := P.hb
    rwa [hb_eq_t] at h'
  exact fourB_not_both H hAt hzt

theorem fourB_AAA (H : FourBHyps a z) (P : FourBPair a p q) {t : G} (ht : t ∈ Gxy p q)
    (ht2 : orderOf t = 2) (h1 : IsConj a t) (h2 : IsConj a (p * t)) (h3 : IsConj a (q * t)) :
    t = (p * q) ^ 2 := by
  have htpp : t ∈ orb2A p p :=
    ⟨(fourB_isConj_iff P.hp).mpr h1, (fourB_isConj_iff P.hp).mpr h2⟩
  have htpq : t ∈ orb2A p q :=
    ⟨(fourB_isConj_iff P.hp).mpr h1, (fourB_isConj_iff P.hp).mpr h3⟩
  have ht_mem : t ∈ orb2A p p ∩ orb2A p q := ⟨htpp, htpq⟩
  obtain ⟨hb, hq4B⟩ := fourB_row H P
  have hset := (H.hPerp p z P.hp (IsConj.refl z)).perp_4B_6A ((p * q) ^ 2) hb q
    (Or.inl hq4B)
  rw [hset] at ht_mem
  have hmem : t ∈ centerOf (Subgroup.closure {p, q}) ∧ t ≠ 1 := by simpa using ht_mem
  have hp2 : p ^ 2 = 1 := fourB_sq_of_orderOf (fourB_orderOf_p H P)
  have hq2 : q ^ 2 = 1 := fourB_sq_of_orderOf (fourB_orderOf_q H P)
  have hord : orderOf (p * q) = 2 * 2 := by rw [fourB_orderOf_pq H P]
  exact (perp_center_closure_pair (k := 2) hp2 hq2 (by norm_num) hord t).mp hmem

end CFSG.EvenSporadicStandard.HNRecog.Section3
