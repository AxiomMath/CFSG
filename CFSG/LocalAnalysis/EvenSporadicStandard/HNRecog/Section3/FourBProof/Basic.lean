module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Hyps

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

private theorem fourB_comm_sq_of_comm {p q g : G} (hp : p * g = g * p) (hq : q * g = g * q) :
    (p * q) ^ 2 * g = g * (p * q) ^ 2 := by
  have hpq : (p * q) * g = g * (p * q) := by
    rw [mul_assoc, hq, ← mul_assoc, hp, mul_assoc]
  exact (show Commute (p * q) g from hpq).pow_left 2

theorem fourB_isConj_iff {y : G} (hp : IsConj a p) : IsConj p y ↔ IsConj a y :=
  ⟨fun h => hp.trans h, fun h => hp.symm.trans h⟩

theorem fourB_orderOf_p (H : FourBHyps a z) (P : FourBPair a p q) : orderOf p = 2 :=
  perp_orderOf_of_isConj_a H.h P.hp

theorem fourB_orderOf_q (H : FourBHyps a z) (P : FourBPair a p q) : orderOf q = 2 :=
  perp_orderOf_of_isConj_a H.h P.hq

theorem fourB_orderOf_b (H : FourBHyps a z) (P : FourBPair a p q) :
    orderOf ((p * q) ^ 2) = 2 :=
  perp_orderOf_of_isConj_a H.h P.hb

theorem fourB_orderOf_pq (H : FourBHyps a z) (P : FourBPair a p q) : orderOf (p * q) = 4 :=
  perp_orderOf_eq_four (fourB_orderOf_b H P)

theorem fourB_mul_self_p (H : FourBHyps a z) (P : FourBPair a p q) : p * p = 1 := by
  have h := pow_orderOf_eq_one p
  rw [fourB_orderOf_p H P] at h
  simpa [pow_two] using h

theorem fourB_mul_self_q (H : FourBHyps a z) (P : FourBPair a p q) : q * q = 1 := by
  have h := pow_orderOf_eq_one q
  rw [fourB_orderOf_q H P] at h
  simpa [pow_two] using h

theorem fourB_sq_swap (H : FourBHyps a z) (P : FourBPair a p q) : (q * p) ^ 2 = (p * q) ^ 2 := by
  have hp1 : p * p = 1 := fourB_mul_self_p H P
  have hq1 : q * q = 1 := fourB_mul_self_q H P
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp1
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq1
  have hqp : q * p = (p * q)⁻¹ := by rw [mul_inv_rev, hqi, hpi]
  have hb2 : ((p * q) ^ 2)⁻¹ = (p * q) ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    have h := pow_orderOf_eq_one ((p * q) ^ 2)
    rw [fourB_orderOf_b H P] at h
    simpa [pow_two] using h
  rw [hqp, inv_pow, hb2]

theorem fourB_pq_ne (H : FourBHyps a z) (P : FourBPair a p q) : p * q ≠ q * p := by
  intro h
  have hp1 : p * p = 1 := fourB_mul_self_p H P
  have hq1 : q * q = 1 := fourB_mul_self_q H P
  have hb1 : (p * q) ^ 2 = 1 := by
    rw [pow_two]
    calc (p * q) * (p * q) = p * (q * p) * q := by group
      _ = p * (p * q) * q := by rw [← h]
      _ = (p * p) * (q * q) := by group
      _ = 1 := by rw [hp1, hq1, mul_one]
  have hb2 := fourB_orderOf_b H P
  rw [hb1, orderOf_one] at hb2
  exact absurd hb2 (by norm_num)

theorem fourB_comm_b_p (H : FourBHyps a z) (P : FourBPair a p q) :
    p * (p * q) ^ 2 = (p * q) ^ 2 * p := by
  have hp1 : p * p = 1 := fourB_mul_self_p H P
  have h1' : p * (p * q) ^ 2 * p = (q * p) ^ 2 := by
    rw [pow_two, pow_two]
    calc p * (p * q * (p * q)) * p = (p * p) * q * p * q * p := by group
      _ = q * p * q * p := by rw [hp1, one_mul]
      _ = q * p * (q * p) := by group
  have h1 : p * (p * q) ^ 2 * p = (p * q) ^ 2 := by
    rw [h1']
    exact fourB_sq_swap H P
  calc p * (p * q) ^ 2 = p * (p * q) ^ 2 * (p * p) := by rw [hp1, mul_one]
    _ = (p * (p * q) ^ 2 * p) * p := by group
    _ = (p * q) ^ 2 * p := by rw [h1]

theorem fourB_comm_b_q (H : FourBHyps a z) (P : FourBPair a p q) :
    q * (p * q) ^ 2 = (p * q) ^ 2 * q := by
  have hq1 : q * q = 1 := fourB_mul_self_q H P
  have h1' : q * (p * q) ^ 2 * q = (q * p) ^ 2 := by
    rw [pow_two, pow_two]
    calc q * (p * q * (p * q)) * q = q * p * q * p * (q * q) := by group
      _ = q * p * q * p := by rw [hq1, mul_one]
      _ = q * p * (q * p) := by group
  have h1 : q * (p * q) ^ 2 * q = (p * q) ^ 2 := by
    rw [h1']
    exact fourB_sq_swap H P
  calc q * (p * q) ^ 2 = q * (p * q) ^ 2 * (q * q) := by rw [hq1, mul_one]
    _ = (q * (p * q) ^ 2 * q) * q := by group
    _ = (p * q) ^ 2 * q := by rw [h1]

theorem fourB_b_mem (H : FourBHyps a z) (P : FourBPair a p q) : (p * q) ^ 2 ∈ Gxy p q := by
  rw [mem_Gxy, mem_Gx, mem_Gx]
  exact ⟨fourB_comm_b_p H P, fourB_comm_b_q H P⟩

theorem fourB_mul_b_p (H : FourBHyps a z) (P : FourBPair a p q) :
    p * (p * q) ^ 2 = q * p * q := by
  have hp1 : p * p = 1 := fourB_mul_self_p H P
  rw [pow_two]
  calc p * (p * q * (p * q)) = (p * p) * q * (p * q) := by group
    _ = q * (p * q) := by rw [hp1, one_mul]
    _ = q * p * q := by group

theorem fourB_mul_b_q (H : FourBHyps a z) (P : FourBPair a p q) :
    q * (p * q) ^ 2 = p * q * p := by
  have hq1 : q * q = 1 := fourB_mul_self_q H P
  rw [← fourB_sq_swap H P]
  rw [pow_two]
  calc q * (q * p * (q * p)) = q * q * p * (q * p) := by group
    _ = p * (q * p) := by rw [hq1, one_mul]
    _ = p * q * p := by group

theorem fourB_isConj_pb (H : FourBHyps a z) (P : FourBPair a p q) :
    IsConj a (p * (p * q) ^ 2) := by
  refine P.hp.trans ?_
  rw [fourB_mul_b_p H P]
  refine isConj_iff.mpr ⟨q, ?_⟩
  rw [inv_eq_of_mul_eq_one_right (fourB_mul_self_q H P)]

theorem fourB_isConj_qb (H : FourBHyps a z) (P : FourBPair a p q) :
    IsConj a (q * (p * q) ^ 2) := by
  refine P.hq.trans ?_
  rw [fourB_mul_b_q H P]
  refine isConj_iff.mpr ⟨p, ?_⟩
  rw [inv_eq_of_mul_eq_one_right (fourB_mul_self_p H P)]

theorem fourB_Gxyz_eq_inf (p t q : G) : Gxyz p t q = Gxy p q ⊓ Gx t := by
  ext g
  simp only [mem_Gxyz, mem_Gxy, Subgroup.mem_inf]
  tauto

theorem fourB_Gxyz_mul_b (p t q : G) : Gxyz p t q = Gxyz p (t * (p * q) ^ 2) q := by
  ext g
  simp only [mem_Gxyz, mem_Gx]
  constructor
  · rintro ⟨hp, ht, hq⟩
    have hb : (p * q) ^ 2 * g = g * (p * q) ^ 2 := fourB_comm_sq_of_comm hp hq
    refine ⟨hp, ?_, hq⟩
    calc t * (p * q) ^ 2 * g = t * ((p * q) ^ 2 * g) := by rw [mul_assoc]
      _ = t * (g * (p * q) ^ 2) := by rw [hb]
      _ = t * g * (p * q) ^ 2 := by rw [mul_assoc]
      _ = g * t * (p * q) ^ 2 := by rw [ht]
      _ = g * (t * (p * q) ^ 2) := by rw [mul_assoc]
  · rintro ⟨hp, ht, hq⟩
    have hb : (p * q) ^ 2 * g = g * (p * q) ^ 2 := fourB_comm_sq_of_comm hp hq
    refine ⟨hp, ?_, hq⟩
    apply mul_right_cancel (b := (p * q) ^ 2)
    calc t * g * (p * q) ^ 2 = t * (g * (p * q) ^ 2) := by rw [mul_assoc]
      _ = t * ((p * q) ^ 2 * g) := by rw [hb]
      _ = t * (p * q) ^ 2 * g := by rw [mul_assoc]
      _ = g * (t * (p * q) ^ 2) := ht
      _ = g * t * (p * q) ^ 2 := by rw [mul_assoc]

theorem fourB_Gxy_le_pb (p q : G) : Gxy p q ≤ Gxy p ((p * q) ^ 2) := by
  intro g hg
  rw [mem_Gxy] at hg
  obtain ⟨hp, hq⟩ := hg
  rw [mem_Gx] at hp hq
  rw [mem_Gxy, mem_Gx, mem_Gx]
  exact ⟨hp, fourB_comm_sq_of_comm hp hq⟩

theorem fourB_Gxy_le_qb (p q : G) : Gxy p q ≤ Gxy q ((p * q) ^ 2) := by
  intro g hg
  rw [mem_Gxy] at hg
  obtain ⟨hp, hq⟩ := hg
  rw [mem_Gx] at hp hq
  rw [mem_Gxy, mem_Gx, mem_Gx]
  exact ⟨hq, fourB_comm_sq_of_comm hp hq⟩

theorem fourB_conj_b {k : G} (hk : k ∈ Gxy p q) : k * (p * q) ^ 2 * k⁻¹ = (p * q) ^ 2 := by
  rw [mem_Gxy] at hk
  obtain ⟨hp, hq⟩ := hk
  rw [mem_Gx] at hp hq
  rw [← fourB_comm_sq_of_comm hp hq]
  group

theorem fourB_row (H : FourBHyps a z) (P : FourBPair a p q) :
    (p * q) ^ 2 ∈ orb2A p p ∧ q ∈ sSet p z ((p * q) ^ 2) 2 := by
  have hpz : IsF5Type p z := isF5Type_of_isConj H.h P.hp (IsConj.refl z)
  have hq4B : q ∈ orb4B p p := by
    show IsConj p q ∧ IsConj p ((p * q) ^ 2)
    exact ⟨(fourB_isConj_iff P.hp).mpr P.hq, (fourB_isConj_iff P.hp).mpr P.hb⟩
  exact tableV_orb4B_row hpz hq4B

theorem fourB_not_both (H : FourBHyps a z) {y : G} (h1 : IsConj a y) (h2 : IsConj z y) : False := by
  exact not_isConj_of_isF5Type H.hI H.h (h1.trans h2.symm)

theorem fourB_comm_of_orders {u t : G} (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hut : orderOf (u * t) = 2) : u * t = t * u := by
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hut2 : (u * t) ^ 2 = 1 := by rw [← hut]; exact pow_orderOf_eq_one (u * t)
  exact comm_of_sq_mul hu2 ht2 hut2

theorem fourB_orderOf_mul_of_comm {u t : G} (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hc : u * t = t * u) (hne : u ≠ t) : orderOf (u * t) = 2 := by
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hu1 : u * u = 1 := by simpa [pow_two] using hu2
  have h2 : (u * t) ^ 2 = 1 := by
    rw [(show Commute u t from hc).mul_pow 2, hu2, ht2, mul_one]
  have hne1 : u * t ≠ 1 := by
    intro h
    apply hne
    calc u = u * 1 := (mul_one u).symm
      _ = u * (u * t) := by rw [h]
      _ = u * u * t := (mul_assoc u u t).symm
      _ = 1 * t := by rw [hu1]
      _ = t := one_mul t
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h2 hne1

theorem fourB_shape_K (H : FourBHyps a z) (P : FourBPair a p q) :
    IsShapeZ2TimesSym 6 ↥(Gxy p q) := by
  have hT5 : TableVFacts p z := H.hT5 p z P.hp (IsConj.refl z)
  refine hT5.shape_4B q ?_
  show IsConj p q ∧ IsConj p ((p * q) ^ 2)
  exact ⟨(fourB_isConj_iff P.hp).mpr P.hq, (fourB_isConj_iff P.hp).mpr P.hb⟩

theorem fourB_comm_of_cls (H : FourBHyps a z) {y t : G} (hy : IsConj a y ∨ IsConj z y)
    (ht : IsConj a t ∨ IsConj z t) (hyt : IsConj a (y * t) ∨ IsConj z (y * t)) :
    y * t = t * y := by
  have hy2 : orderOf y = 2 := hy.elim (perp_orderOf_of_isConj_a H.h) (perp_orderOf_of_isConj_z H.h)
  have ht2 : orderOf t = 2 := ht.elim (perp_orderOf_of_isConj_a H.h) (perp_orderOf_of_isConj_z H.h)
  have hyt2 : orderOf (y * t) = 2 :=
    hyt.elim (perp_orderOf_of_isConj_a H.h) (perp_orderOf_of_isConj_z H.h)
  exact fourB_comm_of_orders hy2 ht2 hyt2

end CFSG.EvenSporadicStandard.HNRecog.Section3
