module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem tableVTrans_orderOf_eq_of_isConj {G : Type} [Group G] {a b : G}
    (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

private theorem tableVTrans_exists_conj_of_exists_conj {G : Type} [Group G] {a x b b' : G}
    (hb : ∃ k ∈ Gx a, k * x * k⁻¹ = b) (hb' : ∃ k ∈ Gx a, k * x * k⁻¹ = b') :
    ∃ k ∈ Gx a, k * b * k⁻¹ = b' := by
  obtain ⟨k, hk, hkb⟩ := hb
  obtain ⟨k', hk', hkb'⟩ := hb'
  refine ⟨k' * k⁻¹, (Gx a).mul_mem hk' ((Gx a).inv_mem hk), ?_⟩
  rw [← hkb, ← hkb']
  group

private theorem tableVTrans_orb2B_conj_az0 (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) {z₀ b₀ u₀ : ↥(Gx a)} (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b₀ u₀)
    (hz₀ : IsConj z (z₀ : G)) (hab₀A : IsConj a (a * b₀)) (hu₀B : IsConj z (u₀ : G))
    {b : G} (hbA : IsConj a b) (habz : IsConj z (a * b)) :
    ∃ k ∈ Gx a, k * (a * z₀ : G) * k⁻¹ = b := by
  have hb_ord : orderOf b = 2 :=
    (tableVTrans_orderOf_eq_of_isConj hbA).symm.trans h.orderOf_a
  have hab_ord : orderOf (a * b) = 2 :=
    (tableVTrans_orderOf_eq_of_isConj habz).symm.trans h.orderOf_z
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb_ord]; exact pow_orderOf_eq_one b
  have hab2 : (a * b) ^ 2 = 1 := by rw [← hab_ord]; exact pow_orderOf_eq_one (a * b)
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hb_ord
    omega
  have hbGx : b ∈ Gx a := mem_Gx.mpr (comm_of_sq_mul ha2 hb2 hab2)
  rcases exists_conj_rep hF hbGx hb2 hb1 with hba | ⟨k, hk, hkb⟩ | ⟨k, hk, hkb⟩ |
    ⟨k, hk, hkb⟩ | ⟨k, hk, hkb⟩
  ·
    exfalso
    have hz1 : IsConj z (1 : G) := by
      have h := habz
      rw [hba] at h
      rwa [show a * a = 1 from by rw [← pow_two]; exact ha2] at h
    have hord := tableVTrans_orderOf_eq_of_isConj hz1
    rw [h.orderOf_z, orderOf_one] at hord
    omega
  ·
    exfalso
    exact not_isConj_of_isF5Type hI h (hbA.trans (hz₀.trans (isConj_iff.mpr ⟨k, hkb⟩)).symm)
  ·
    exact ⟨k, hk, hkb⟩
  ·
    exfalso
    have hkfix : k * a * k⁻¹ = a := by
      rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
    have hmc : a * b = k * (a * (b₀ : G)) * k⁻¹ := by
      rw [← hkb]; exact mul_conj_of_fix hkfix
    have ha_b : IsConj a (a * b) := hab₀A.trans (isConj_iff.mpr ⟨k, hmc.symm⟩)
    exact not_isConj_of_isF5Type hI h (ha_b.trans habz.symm)
  ·
    exfalso
    exact not_isConj_of_isF5Type hI h (hbA.trans (hu₀B.trans (isConj_iff.mpr ⟨k, hkb⟩)).symm)

private theorem tableVTrans_orb2AB_conj_z0 (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) {z₀ b₀ u₀ : ↥(Gx a)} (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b₀ u₀)
    (hz₀a : IsConj a (a * z₀)) (hb₀A : IsConj a (b₀ : G)) (hau₀B : IsConj z (a * u₀))
    {w : G} (hwz : IsConj z w) (hawA : IsConj a (a * w)) :
    ∃ k ∈ Gx a, k * (z₀ : G) * k⁻¹ = w := by
  have hw_ord : orderOf w = 2 :=
    (tableVTrans_orderOf_eq_of_isConj hwz).symm.trans h.orderOf_z
  have haw_ord : orderOf (a * w) = 2 :=
    (tableVTrans_orderOf_eq_of_isConj hawA).symm.trans h.orderOf_a
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hw2 : w ^ 2 = 1 := by rw [← hw_ord]; exact pow_orderOf_eq_one w
  have haw2 : (a * w) ^ 2 = 1 := by rw [← haw_ord]; exact pow_orderOf_eq_one (a * w)
  have hw1 : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hw_ord
    omega
  have hwGx : w ∈ Gx a := mem_Gx.mpr (comm_of_sq_mul ha2 hw2 haw2)
  rcases exists_conj_rep hF hwGx hw2 hw1 with hwa | ⟨k, hk, hkw⟩ | ⟨k, hk, hkw⟩ |
    ⟨k, hk, hkw⟩ | ⟨k, hk, hkw⟩
  ·
    exfalso
    have hza : IsConj z a := by
      have h := hwz
      rwa [hwa] at h
    exact not_isConj_of_isF5Type hI h hza.symm
  ·
    exact ⟨k, hk, hkw⟩
  ·
    exfalso
    have ha_w : IsConj a w := hz₀a.trans (isConj_iff.mpr ⟨k, hkw⟩)
    exact not_isConj_of_isF5Type hI h (ha_w.trans hwz.symm)
  ·
    exfalso
    have ha_w : IsConj a w := hb₀A.trans (isConj_iff.mpr ⟨k, hkw⟩)
    exact not_isConj_of_isF5Type hI h (ha_w.trans hwz.symm)
  ·
    exfalso
    have hkfix : k * a * k⁻¹ = a := by
      rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
    have hmc : a * w = k * (a * (u₀ : G)) * k⁻¹ := by
      rw [← hkw]; exact mul_conj_of_fix hkfix
    have hz_aw : IsConj z (a * w) := hau₀B.trans (isConj_iff.mpr ⟨k, hmc.symm⟩)
    exact not_isConj_of_isF5Type hI h (hawA.trans hz_aw.symm)

theorem tableV_exists_conj_orb2B (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) {b b' : G}
    (hb : b ∈ orb2B a z a) (hb' : b' ∈ orb2B a z a) : ∃ k ∈ Gx a, k * b * k⁻¹ = b' := by
  obtain ⟨z₀, b₀, u₀, hF, hz₀, -, -, -, -, -⟩ := hF1.rep_z
  obtain ⟨⟨-, hab₀A, -, -⟩, ⟨hu₀B, -, -, -, -, -, -⟩⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  exact tableVTrans_exists_conj_of_exists_conj
    (tableVTrans_orb2B_conj_az0 hI h hF hz₀ hab₀A hu₀B hb.1 hb.2)
    (tableVTrans_orb2B_conj_az0 hI h hF hz₀ hab₀A hu₀B hb'.1 hb'.2)

theorem tableV_exists_conj_orb2AB (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) {w w' : G}
    (hw : w ∈ orb2AB a z a) (hw' : w' ∈ orb2AB a z a) : ∃ k ∈ Gx a, k * w * k⁻¹ = w' := by
  obtain ⟨z₀, b₀, u₀, hF, hz₀, hz₀a, -, -, -, -⟩ := hF1.rep_z
  obtain ⟨⟨hb₀A, -, -, -⟩, ⟨-, hau₀B, -, -, -, -, -⟩⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  exact tableVTrans_exists_conj_of_exists_conj
    (tableVTrans_orb2AB_conj_z0 hI h hF hz₀a hb₀A hau₀B hw.1 hw.2)
    (tableVTrans_orb2AB_conj_z0 hI h hF hz₀a hb₀A hau₀B hw'.1 hw'.2)

end CFSG.EvenSporadicStandard.HNRecog.Section3
