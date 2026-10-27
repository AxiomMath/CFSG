module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cDV

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

structure Sec11cCnt (G : Type) [Group G] (z : G) (R T C D Q1 Q2 : Subgroup G) (a x : G) :
    Prop where
  cnt : Sec11Cnt G z T C Q1 Q2 a x
  T_le : T ≤ R
  C_le : C ≤ D
  D_le : D ≤ R
  R_two : IsPGroup 2 R
  R_z : ∀ g ∈ R, g * z = z * g
  R_normD : ∀ g ∈ R, ∀ d ∈ D, g * d * g⁻¹ ∈ D
  R_normQ : ∀ g ∈ R, ∀ q ∈ Q1 ⊔ Q2, g * q * g⁻¹ ∈ Q1 ⊔ Q2
  D_Q : ∀ d ∈ D, ∀ q ∈ Q1 ⊔ Q2, d * q = q * d
  D_inf : D ⊓ (Q1 ⊔ Q2) = zpowers z
  Q_el : IsElemAbelianMod z (Q1 ⊔ Q2)
  R_bar : ∀ g ∈ R, (∀ q ∈ Q1 ⊔ Q2, g * q * g⁻¹ * q⁻¹ ∈ zpowers z) → g ∈ D ⊔ (Q1 ⊔ Q2)

namespace Sec11cCnt

variable {z : G} {R T C D Q1 Q2 : Subgroup G} {a x : G}

private theorem cCtx_conj_eq_of_mem_zpowers {y z u : G} (hyz : y * z = z * y)
    (hu : u ∈ zpowers z) : y * u * y⁻¹ = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [show y * z ^ k = z ^ k * y from ((show Commute y z from hyz).zpow_right k).eq]
  group

theorem z_memD (h : Sec11cCnt G z R T C D Q1 Q2 a x) : z ∈ D := by
  have hz : z ∈ D ⊓ (Q1 ⊔ Q2) := h.D_inf.symm ▸ Subgroup.mem_zpowers z
  exact (Subgroup.mem_inf.mp hz).1

theorem z_memQ (h : Sec11cCnt G z R T C D Q1 Q2 a x) : z ∈ Q1 ⊔ Q2 := by
  have hz : z ∈ D ⊓ (Q1 ⊔ Q2) := h.D_inf.symm ▸ Subgroup.mem_zpowers z
  exact (Subgroup.mem_inf.mp hz).2

theorem Q_le_T (h : Sec11cCnt G z R T C D Q1 Q2 a x) : Q1 ⊔ Q2 ≤ T :=
  sup_le h.cnt.Q1_le h.cnt.Q2_le

theorem TD_le (h : Sec11cCnt G z R T C D Q1 Q2 a x) : T ⊔ D ≤ R :=
  sup_le h.T_le h.D_le

theorem DQ_le_TD (h : Sec11cCnt G z R T C D Q1 Q2 a x) : D ⊔ (Q1 ⊔ Q2) ≤ T ⊔ D :=
  sup_le le_sup_right (h.Q_le_T.trans le_sup_left)

theorem card_Q [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) : Nat.card ↥(Q1 ⊔ Q2) = 32 := by
  have hzcard : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers,
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact h.cnt.z_sq) h.cnt.z_ne]
  obtain ⟨hQ, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute Q1 Q2 h.cnt.Q_comm
  rw [h.cnt.Q_inf, hzcard, h.cnt.Q1_card, h.cnt.Q2_card] at hQ
  apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
  norm_num at hQ ⊢
  exact hQ

theorem DQ_normQ1 (h : Sec11cCnt G z R T C D Q1 Q2 a x) {w : G} (hw : w ∈ D ⊔ (Q1 ⊔ Q2)) :
    ∀ q ∈ Q1, w * q * w⁻¹ ∈ Q1 := by
  intro q hq
  obtain ⟨d, hd, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.D_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.cnt.Q_comm hw'
  rw [hww', hw'q]
  have hv : q1 * q * q1⁻¹ ∈ Q1 := Q1.mul_mem (Q1.mul_mem hq1 hq) (Q1.inv_mem hq1)
  have hconj : (q1 * q2) * q * (q1 * q2)⁻¹ = q1 * q * q1⁻¹ := by
    have hc2 : q2 * (q1 * q * q1⁻¹) = (q1 * q * q1⁻¹) * q2 :=
      (h.cnt.Q_comm (q1 * q * q1⁻¹) hv q2 hq2).symm
    calc (q1 * q2) * q * (q1 * q2)⁻¹
        = q2 * (q1 * q * q1⁻¹) * q2⁻¹ := by
          rw [h.cnt.Q_comm q1 hq1 q2 hq2]; group
      _ = q1 * q * q1⁻¹ := by rw [hc2]; group
  have hfull : (d * (q1 * q2)) * q * (d * (q1 * q2))⁻¹ = q1 * q * q1⁻¹ := by
    have e1 : (d * (q1 * q2)) * q * (d * (q1 * q2))⁻¹
        = d * ((q1 * q2) * q * (q1 * q2)⁻¹) * d⁻¹ := by group
    have e2 : d * (q1 * q * q1⁻¹) * d⁻¹ = q1 * q * q1⁻¹ := by
      rw [h.D_Q d hd (q1 * q * q1⁻¹) (Subgroup.mem_sup_left hv)]; group
    rw [e1, hconj, e2]
  rw [hfull]
  exact hv

theorem DQ_normQ2 (h : Sec11cCnt G z R T C D Q1 Q2 a x) {w : G} (hw : w ∈ D ⊔ (Q1 ⊔ Q2)) :
    ∀ q ∈ Q2, w * q * w⁻¹ ∈ Q2 := by
  intro q hq
  obtain ⟨d, hd, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.D_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.cnt.Q_comm hw'
  rw [hww', hw'q]
  have hv : q2 * q * q2⁻¹ ∈ Q2 := Q2.mul_mem (Q2.mul_mem hq2 hq) (Q2.inv_mem hq2)
  have hconj : (q1 * q2) * q * (q1 * q2)⁻¹ = q2 * q * q2⁻¹ := by
    have hc1 : q1 * (q2 * q * q2⁻¹) = (q2 * q * q2⁻¹) * q1 :=
      h.cnt.Q_comm q1 hq1 (q2 * q * q2⁻¹) hv
    calc (q1 * q2) * q * (q1 * q2)⁻¹
        = q1 * (q2 * q * q2⁻¹) * q1⁻¹ := by group
      _ = q2 * q * q2⁻¹ := by rw [hc1]; group
  have hfull : (d * (q1 * q2)) * q * (d * (q1 * q2))⁻¹ = q2 * q * q2⁻¹ := by
    have e1 : (d * (q1 * q2)) * q * (d * (q1 * q2))⁻¹
        = d * ((q1 * q2) * q * (q1 * q2)⁻¹) * d⁻¹ := by group
    have e2 : d * (q2 * q * q2⁻¹) * d⁻¹ = q2 * q * q2⁻¹ := by
      rw [h.D_Q d hd (q2 * q * q2⁻¹) (Subgroup.mem_sup_right hv)]; group
    rw [e1, hconj, e2]
  rw [hfull]
  exact hv

theorem nt1 (h : Sec11cCnt G z R T C D Q1 Q2 a x) {w : G} (hw : w ∈ D ⊔ (Q1 ⊔ Q2)) :
    ∃ y ∈ Q1, (x * w) * y * (x * w)⁻¹ * y⁻¹ ∉ zpowers z := by
  obtain ⟨y, hy, hxy⟩ := h.cnt.x_nt1
  refine ⟨y, hy, fun hmem => hxy ?_⟩
  obtain ⟨d, hd, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.D_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.cnt.Q_comm hw'
  set u : G := q1 * y * q1⁻¹ * y⁻¹ with hu_def
  have hu : u ∈ zpowers z := h.cnt.Q1_el q1 hq1 y hy
  have huQ1 : u * y ∈ Q1 := by
    have heq : u * y = q1 * y * q1⁻¹ := by rw [hu_def]; group
    rw [heq]
    exact Q1.mul_mem (Q1.mul_mem hq1 hy) (Q1.inv_mem hq1)
  have hwuy : w * y * w⁻¹ = u * y := by
    have hinner : (q1 * q2) * y * (q1 * q2)⁻¹ = u * y := by
      have hq2y : q2 * y = y * q2 := (h.cnt.Q_comm y hy q2 hq2).symm
      calc (q1 * q2) * y * (q1 * q2)⁻¹
          = q1 * (q2 * y * q2⁻¹) * q1⁻¹ := by group
        _ = q1 * y * q1⁻¹ := by rw [hq2y]; group
        _ = u * y := by rw [hu_def]; group
    calc w * y * w⁻¹ = (d * w') * y * (d * w')⁻¹ := by rw [hww']
      _ = d * (w' * y * w'⁻¹) * d⁻¹ := by group
      _ = d * ((q1 * q2) * y * (q1 * q2)⁻¹) * d⁻¹ := by rw [hw'q]
      _ = d * (u * y) * d⁻¹ := by rw [hinner]
      _ = u * y := by
          rw [h.D_Q d hd (u * y) (Subgroup.mem_sup_left huQ1)]
          group
  have hxu : x * u * x⁻¹ = u :=
    cCtx_conj_eq_of_mem_zpowers (h.cnt.z_cent x h.cnt.x_mem) hu
  have hid : (x * w) * y * (x * w)⁻¹ * y⁻¹ = u * (x * y * x⁻¹ * y⁻¹) := by
    have e1 : (x * w) * y * (x * w)⁻¹ * y⁻¹ = x * (w * y * w⁻¹) * x⁻¹ * y⁻¹ := by group
    have e2 : x * (u * y) * x⁻¹ * y⁻¹ = (x * u * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e1, hwuy, e2, hxu]
  rw [hid] at hmem
  have hv : x * y * x⁻¹ * y⁻¹ = u⁻¹ * (u * (x * y * x⁻¹ * y⁻¹)) := by group
  rw [hv]
  exact (zpowers z).mul_mem ((zpowers z).inv_mem hu) hmem

theorem nt2 (h : Sec11cCnt G z R T C D Q1 Q2 a x) {w : G} (hw : w ∈ D ⊔ (Q1 ⊔ Q2)) :
    ∃ y ∈ Q2, (x * w) * y * (x * w)⁻¹ * y⁻¹ ∉ zpowers z := by
  obtain ⟨y, hy, hxy⟩ := h.cnt.x_nt2
  refine ⟨y, hy, fun hmem => hxy ?_⟩
  obtain ⟨d, hd, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.D_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.cnt.Q_comm hw'
  set u : G := q2 * y * q2⁻¹ * y⁻¹ with hu_def
  have hu : u ∈ zpowers z := h.cnt.Q2_el q2 hq2 y hy
  have huQ2 : u * y ∈ Q2 := by
    have heq : u * y = q2 * y * q2⁻¹ := by rw [hu_def]; group
    rw [heq]
    exact Q2.mul_mem (Q2.mul_mem hq2 hy) (Q2.inv_mem hq2)
  have hwuy : w * y * w⁻¹ = u * y := by
    have hinner : (q1 * q2) * y * (q1 * q2)⁻¹ = u * y := by
      have hcomm1 : q1 * (q2 * y * q2⁻¹) = (q2 * y * q2⁻¹) * q1 :=
        h.cnt.Q_comm q1 hq1 (q2 * y * q2⁻¹)
          (Q2.mul_mem (Q2.mul_mem hq2 hy) (Q2.inv_mem hq2))
      calc (q1 * q2) * y * (q1 * q2)⁻¹
          = q1 * (q2 * y * q2⁻¹) * q1⁻¹ := by group
        _ = q2 * y * q2⁻¹ := by rw [hcomm1]; group
        _ = u * y := by rw [hu_def]; group
    calc w * y * w⁻¹ = (d * w') * y * (d * w')⁻¹ := by rw [hww']
      _ = d * (w' * y * w'⁻¹) * d⁻¹ := by group
      _ = d * ((q1 * q2) * y * (q1 * q2)⁻¹) * d⁻¹ := by rw [hw'q]
      _ = d * (u * y) * d⁻¹ := by rw [hinner]
      _ = u * y := by
          rw [h.D_Q d hd (u * y) (Subgroup.mem_sup_right huQ2)]
          group
  have hxu : x * u * x⁻¹ = u :=
    cCtx_conj_eq_of_mem_zpowers (h.cnt.z_cent x h.cnt.x_mem) hu
  have hid : (x * w) * y * (x * w)⁻¹ * y⁻¹ = u * (x * y * x⁻¹ * y⁻¹) := by
    have e1 : (x * w) * y * (x * w)⁻¹ * y⁻¹ = x * (w * y * w⁻¹) * x⁻¹ * y⁻¹ := by group
    have e2 : x * (u * y) * x⁻¹ * y⁻¹ = (x * u * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e1, hwuy, e2, hxu]
  rw [hid] at hmem
  have hv : x * y * x⁻¹ * y⁻¹ = u⁻¹ * (u * (x * y * x⁻¹ * y⁻¹)) := by group
  rw [hv]
  exact (zpowers z).mul_mem ((zpowers z).inv_mem hu) hmem

theorem DQ_norm (h : Sec11cCnt G z R T C D Q1 Q2 a x) :
    ∀ g ∈ R, ∀ w ∈ D ⊔ (Q1 ⊔ Q2), g * w * g⁻¹ ∈ D ⊔ (Q1 ⊔ Q2) := by
  intro g hg w hw
  obtain ⟨d, hd, q, hq, hdq⟩ := exists_mul_of_mem_sup_of_commute h.D_Q hw
  rw [hdq]
  have he : g * (d * q) * g⁻¹ = (g * d * g⁻¹) * (g * q * g⁻¹) := by group
  rw [he]
  exact Subgroup.mul_mem_sup (h.R_normD g hg d hd) (h.R_normQ g hg q hq)

theorem cover (h : Sec11cCnt G z R T C D Q1 Q2 a x) :
    ∀ g ∈ T ⊔ D, g ∈ D ⊔ (Q1 ⊔ Q2) ∨
      ∃ w ∈ D ⊔ (Q1 ⊔ Q2), g = a * w ∨ g = x * w ∨ g = a * x * w := by
  have hTn : T ≤ Subgroup.normalizer D := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun hd => h.R_normD t (h.T_le ht) d hd, fun hd => ?_⟩
    have h2 := h.R_normD t⁻¹ (R.inv_mem (h.T_le ht)) (t * d * t⁻¹) hd
    convert h2 using 1
    group
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right T D hTn
  have hDQs : C ⊔ (Q1 ⊔ Q2) ≤ D ⊔ (Q1 ⊔ Q2) := sup_le_sup_right h.C_le (Q1 ⊔ Q2)
  intro g hg
  have hgmem : g ∈ ((T : Set G) * (D : Set G) : Set G) := by
    rw [← hcoe]
    exact hg
  obtain ⟨s, hs, d, hd, hsd⟩ := Set.mem_mul.mp hgmem
  rcases h.cnt.cover s hs with hsW | ⟨w, hw, hwform⟩
  · left
    rw [← hsd]
    exact (D ⊔ (Q1 ⊔ Q2)).mul_mem (hDQs hsW) (Subgroup.mem_sup_left hd)
  · have hwd : w * d ∈ D ⊔ (Q1 ⊔ Q2) :=
      (D ⊔ (Q1 ⊔ Q2)).mul_mem (hDQs hw) (Subgroup.mem_sup_left hd)
    rcases hwform with hsw | hsw | hsw
    · right
      exact ⟨w * d, hwd, Or.inl (by rw [← hsd, hsw]; group)⟩
    · right
      exact ⟨w * d, hwd, Or.inr (Or.inl (by rw [← hsd, hsw]; group))⟩
    · right
      exact ⟨w * d, hwd, Or.inr (Or.inr (by rw [← hsd, hsw]; group))⟩

theorem card_Qg_le [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) {g : G} (hg : g ∈ R)
    (hgDQ : g ∉ D ⊔ (Q1 ⊔ Q2)) : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 16 := by
  by_contra hle
  rw [not_le] at hle
  have hdvd : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ∣ 2 ^ 5 := by
    rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← h.card_Q]
    exact Subgroup.card_dvd_of_le (sec11Qg_le z g (Q1 ⊔ Q2))
  obtain ⟨k, hk5, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp hdvd
  have hk_eq : k = 5 := by
    have hle' : 16 < 2 ^ k := by rwa [hk] at hle
    have hk_ge : 5 ≤ k := by
      by_contra hlt
      have hk4 : k ≤ 4 := by omega
      have hpow : 2 ^ k ≤ 2 ^ 4 := by gcongr
      norm_num at hpow
      omega
    omega
  have hcard32 : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) = 32 := by
    rw [hk, hk_eq]; norm_num
  have hQg_eq : sec11Qg z g (Q1 ⊔ Q2) = Q1 ⊔ Q2 := by
    refine Subgroup.eq_of_le_of_card_ge (sec11Qg_le z g (Q1 ⊔ Q2)) ?_
    rw [hcard32, h.card_Q]
  refine hgDQ (h.R_bar g hg ?_)
  intro q hq
  have hq' : q ∈ sec11Qg z g (Q1 ⊔ Q2) := by rw [hQg_eq]; exact hq
  rw [mem_sec11Qg_iff] at hq'
  exact hq'.2.2

theorem proj (h : Sec11cCnt G z R T C D Q1 Q2 a x) {V : Subgroup G} (hVR : V ≤ R)
    (hV : IsElemAbelianMod z V) : Sec11cProj G z D (Q1 ⊔ Q2) V where
  DQ_comm := h.D_Q
  inf_eq := h.D_inf
  z_memD := h.z_memD
  z_memQ := h.z_memQ
  Q_z := fun q hq => h.cnt.z_cent q (h.Q_le_T hq)
  Q_el := h.Q_el
  V_normD := fun v hv d hd => h.R_normD v (hVR hv) d hd
  V_normQ := fun v hv q hq => h.R_normQ v (hVR hv) q hq
  V_z := fun v hv => h.R_z v (hVR hv)
  V_el := hV

end Sec11cCnt

end CFSG.OddStandard.SmallF3.Omega
