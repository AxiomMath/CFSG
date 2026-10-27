module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Cov
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117TC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec11Cnt (G : Type) [Group G] (z : G) (T C Q1 Q2 : Subgroup G) (a x : G) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_cent : ∀ g ∈ T, g * z = z * g
  Q1_le : Q1 ≤ T
  Q2_le : Q2 ≤ T
  Q_comm : ∀ p ∈ Q1, ∀ q ∈ Q2, p * q = q * p
  Q_inf : Q1 ⊓ Q2 = zpowers z
  Q1_card : Nat.card Q1 = 8
  Q2_card : Nat.card Q2 = 8
  Q1_el : ∀ p ∈ Q1, ∀ q ∈ Q1, p * q * p⁻¹ * q⁻¹ ∈ zpowers z
  Q2_el : ∀ p ∈ Q2, ∀ q ∈ Q2, p * q * p⁻¹ * q⁻¹ ∈ zpowers z
  T_normQ : ∀ g ∈ T, ∀ q ∈ Q1 ⊔ Q2, g * q * g⁻¹ ∈ Q1 ⊔ Q2
  C_comm : ∀ c ∈ C, ∀ c' ∈ C, c * c' * c⁻¹ * c'⁻¹ ∈ zpowers z
  C_Q : ∀ c ∈ C, ∀ q ∈ Q1 ⊔ Q2, c * q = q * c
  C_inf : C ⊓ (Q1 ⊔ Q2) = zpowers z
  W_norm : ∀ g ∈ T, ∀ w ∈ C ⊔ (Q1 ⊔ Q2), g * w * g⁻¹ ∈ C ⊔ (Q1 ⊔ Q2)
  a_mem : a ∈ T
  a_sq : a * a = 1
  a_C : ∀ c ∈ C, a * c = c * a
  a_swap : ∀ q ∈ Q2, a * q * a⁻¹ ∈ Q1
  x_mem : x ∈ T
  x_sq : x * x = 1
  x_C : ∀ c ∈ C, x * c * x⁻¹ * c⁻¹ ∈ zpowers z
  x_norm1 : ∀ q ∈ Q1, x * q * x⁻¹ ∈ Q1
  x_norm2 : ∀ q ∈ Q2, x * q * x⁻¹ ∈ Q2
  x_nt1 : ∃ y ∈ Q1, x * y * x⁻¹ * y⁻¹ ∉ zpowers z
  x_nt2 : ∃ y ∈ Q2, x * y * x⁻¹ * y⁻¹ ∉ zpowers z
  ax_W : a * x * a⁻¹ * x⁻¹ ∈ C ⊔ (Q1 ⊔ Q2)
  gen : T = Subgroup.closure
    ((C : Set G) ∪ ((Q1 ⊔ Q2 : Subgroup G) : Set G) ∪ ({a, x} : Set G))

namespace Sec11Cnt

variable {z : G} {T C Q1 Q2 : Subgroup G} {a x : G}

private theorem cnt_card_zpowers_eq_two {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rwa [pow_two]) hz1]

private theorem cnt_conj_eq_of_mem_zpowers {y z u : G} (hyz : y * z = z * y)
    (hu : u ∈ zpowers z) : y * u * y⁻¹ = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [show y * z ^ k = z ^ k * y from ((show Commute y z from hyz).zpow_right k).eq]
  group

theorem card_W [Finite G] (h : Sec11Cnt G z T C Q1 Q2 a x) :
    Nat.card ↥(C ⊔ (Q1 ⊔ Q2)) = 16 * Nat.card C := by
  have hzcard : Nat.card ↥(zpowers z) = 2 := cnt_card_zpowers_eq_two h.z_sq h.z_ne
  obtain ⟨hQ, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute Q1 Q2 h.Q_comm
  rw [h.Q_inf, hzcard, h.Q1_card, h.Q2_card] at hQ
  have hQ' : Nat.card ↥(Q1 ⊔ Q2) = 32 := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    norm_num at hQ ⊢
    exact hQ
  obtain ⟨hW, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute C (Q1 ⊔ Q2) h.C_Q
  rw [h.C_inf, hzcard, hQ'] at hW
  apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
  rw [hW]
  ring

theorem W_normQ1 (h : Sec11Cnt G z T C Q1 Q2 a x) {w : G} (hw : w ∈ C ⊔ (Q1 ⊔ Q2)) :
    ∀ q ∈ Q1, w * q * w⁻¹ ∈ Q1 := by
  intro q hq
  obtain ⟨c, hc, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.C_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.Q_comm hw'
  rw [hww', hw'q]
  have hv : q1 * q * q1⁻¹ ∈ Q1 := Q1.mul_mem (Q1.mul_mem hq1 hq) (Q1.inv_mem hq1)
  have hconj : (q1 * q2) * q * (q1 * q2)⁻¹ = q1 * q * q1⁻¹ := by
    have hc2 : q2 * (q1 * q * q1⁻¹) = (q1 * q * q1⁻¹) * q2 :=
      (h.Q_comm (q1 * q * q1⁻¹) hv q2 hq2).symm
    calc (q1 * q2) * q * (q1 * q2)⁻¹
        = q2 * (q1 * q * q1⁻¹) * q2⁻¹ := by
          rw [h.Q_comm q1 hq1 q2 hq2]; group
      _ = q1 * q * q1⁻¹ := by rw [hc2]; group
  have hfull : (c * (q1 * q2)) * q * (c * (q1 * q2))⁻¹ = q1 * q * q1⁻¹ := by
    have e1 : (c * (q1 * q2)) * q * (c * (q1 * q2))⁻¹
        = c * ((q1 * q2) * q * (q1 * q2)⁻¹) * c⁻¹ := by group
    have e2 : c * (q1 * q * q1⁻¹) * c⁻¹ = q1 * q * q1⁻¹ := by
      rw [h.C_Q c hc (q1 * q * q1⁻¹) (Subgroup.mem_sup_left hv)]; group
    rw [e1, hconj, e2]
  rw [hfull]
  exact hv

theorem W_normQ2 (h : Sec11Cnt G z T C Q1 Q2 a x) {w : G} (hw : w ∈ C ⊔ (Q1 ⊔ Q2)) :
    ∀ q ∈ Q2, w * q * w⁻¹ ∈ Q2 := by
  intro q hq
  obtain ⟨c, hc, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.C_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.Q_comm hw'
  rw [hww', hw'q]
  have hv : q2 * q * q2⁻¹ ∈ Q2 := Q2.mul_mem (Q2.mul_mem hq2 hq) (Q2.inv_mem hq2)
  have hconj : (q1 * q2) * q * (q1 * q2)⁻¹ = q2 * q * q2⁻¹ := by
    have hc1 : q1 * (q2 * q * q2⁻¹) = (q2 * q * q2⁻¹) * q1 :=
      h.Q_comm q1 hq1 (q2 * q * q2⁻¹) hv
    calc (q1 * q2) * q * (q1 * q2)⁻¹
        = q1 * (q2 * q * q2⁻¹) * q1⁻¹ := by group
      _ = q2 * q * q2⁻¹ := by rw [hc1]; group
  have hfull : (c * (q1 * q2)) * q * (c * (q1 * q2))⁻¹ = q2 * q * q2⁻¹ := by
    have e1 : (c * (q1 * q2)) * q * (c * (q1 * q2))⁻¹
        = c * ((q1 * q2) * q * (q1 * q2)⁻¹) * c⁻¹ := by group
    have e2 : c * (q2 * q * q2⁻¹) * c⁻¹ = q2 * q * q2⁻¹ := by
      rw [h.C_Q c hc (q2 * q * q2⁻¹) (Subgroup.mem_sup_right hv)]; group
    rw [e1, hconj, e2]
  rw [hfull]
  exact hv

theorem nt1 (h : Sec11Cnt G z T C Q1 Q2 a x) {w : G} (hw : w ∈ C ⊔ (Q1 ⊔ Q2)) :
    ∃ y ∈ Q1, (x * w) * y * (x * w)⁻¹ * y⁻¹ ∉ zpowers z := by
  obtain ⟨y, hy, hxy⟩ := h.x_nt1
  refine ⟨y, hy, fun hmem => hxy ?_⟩
  obtain ⟨c, hc, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.C_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.Q_comm hw'
  set u : G := q1 * y * q1⁻¹ * y⁻¹ with hu_def
  have hu : u ∈ zpowers z := h.Q1_el q1 hq1 y hy
  have huQ1 : u * y ∈ Q1 := by
    have heq : u * y = q1 * y * q1⁻¹ := by rw [hu_def]; group
    rw [heq]
    exact Q1.mul_mem (Q1.mul_mem hq1 hy) (Q1.inv_mem hq1)
  have hwuy : w * y * w⁻¹ = u * y := by
    have hinner : (q1 * q2) * y * (q1 * q2)⁻¹ = u * y := by
      have hq2y : q2 * y = y * q2 := (h.Q_comm y hy q2 hq2).symm
      calc (q1 * q2) * y * (q1 * q2)⁻¹
          = q1 * (q2 * y * q2⁻¹) * q1⁻¹ := by group
        _ = q1 * y * q1⁻¹ := by rw [hq2y]; group
        _ = u * y := by rw [hu_def]; group
    calc w * y * w⁻¹ = (c * w') * y * (c * w')⁻¹ := by rw [hww']
      _ = c * (w' * y * w'⁻¹) * c⁻¹ := by group
      _ = c * ((q1 * q2) * y * (q1 * q2)⁻¹) * c⁻¹ := by rw [hw'q]
      _ = c * (u * y) * c⁻¹ := by rw [hinner]
      _ = u * y := by
          rw [h.C_Q c hc (u * y) (Subgroup.mem_sup_left huQ1)]
          group
  have hxu : x * u * x⁻¹ = u :=
    cnt_conj_eq_of_mem_zpowers (h.z_cent x h.x_mem) hu
  have hid : (x * w) * y * (x * w)⁻¹ * y⁻¹ = u * (x * y * x⁻¹ * y⁻¹) := by
    have e1 : (x * w) * y * (x * w)⁻¹ * y⁻¹ = x * (w * y * w⁻¹) * x⁻¹ * y⁻¹ := by group
    have e2 : x * (u * y) * x⁻¹ * y⁻¹ = (x * u * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e1, hwuy, e2, hxu]
  rw [hid] at hmem
  have hv : x * y * x⁻¹ * y⁻¹ = u⁻¹ * (u * (x * y * x⁻¹ * y⁻¹)) := by group
  rw [hv]
  exact (zpowers z).mul_mem ((zpowers z).inv_mem hu) hmem

theorem nt2 (h : Sec11Cnt G z T C Q1 Q2 a x) {w : G} (hw : w ∈ C ⊔ (Q1 ⊔ Q2)) :
    ∃ y ∈ Q2, (x * w) * y * (x * w)⁻¹ * y⁻¹ ∉ zpowers z := by
  obtain ⟨y, hy, hxy⟩ := h.x_nt2
  refine ⟨y, hy, fun hmem => hxy ?_⟩
  obtain ⟨c, hc, w', hw', hww'⟩ := exists_mul_of_mem_sup_of_commute h.C_Q hw
  obtain ⟨q1, hq1, q2, hq2, hw'q⟩ := exists_mul_of_mem_sup_of_commute h.Q_comm hw'
  set u : G := q2 * y * q2⁻¹ * y⁻¹ with hu_def
  have hu : u ∈ zpowers z := h.Q2_el q2 hq2 y hy
  have huQ2 : u * y ∈ Q2 := by
    have heq : u * y = q2 * y * q2⁻¹ := by rw [hu_def]; group
    rw [heq]
    exact Q2.mul_mem (Q2.mul_mem hq2 hy) (Q2.inv_mem hq2)
  have hwuy : w * y * w⁻¹ = u * y := by
    have hinner : (q1 * q2) * y * (q1 * q2)⁻¹ = u * y := by
      have hcomm1 : q1 * (q2 * y * q2⁻¹) = (q2 * y * q2⁻¹) * q1 :=
        h.Q_comm q1 hq1 (q2 * y * q2⁻¹) (Q2.mul_mem (Q2.mul_mem hq2 hy) (Q2.inv_mem hq2))
      calc (q1 * q2) * y * (q1 * q2)⁻¹
          = q1 * (q2 * y * q2⁻¹) * q1⁻¹ := by group
        _ = q2 * y * q2⁻¹ := by rw [hcomm1]; group
        _ = u * y := by rw [hu_def]; group
    calc w * y * w⁻¹ = (c * w') * y * (c * w')⁻¹ := by rw [hww']
      _ = c * (w' * y * w'⁻¹) * c⁻¹ := by group
      _ = c * ((q1 * q2) * y * (q1 * q2)⁻¹) * c⁻¹ := by rw [hw'q]
      _ = c * (u * y) * c⁻¹ := by rw [hinner]
      _ = u * y := by
          rw [h.C_Q c hc (u * y) (Subgroup.mem_sup_right huQ2)]
          group
  have hxu : x * u * x⁻¹ = u :=
    cnt_conj_eq_of_mem_zpowers (h.z_cent x h.x_mem) hu
  have hid : (x * w) * y * (x * w)⁻¹ * y⁻¹ = u * (x * y * x⁻¹ * y⁻¹) := by
    have e1 : (x * w) * y * (x * w)⁻¹ * y⁻¹ = x * (w * y * w⁻¹) * x⁻¹ * y⁻¹ := by group
    have e2 : x * (u * y) * x⁻¹ * y⁻¹ = (x * u * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e1, hwuy, e2, hxu]
  rw [hid] at hmem
  have hv : x * y * x⁻¹ * y⁻¹ = u⁻¹ * (u * (x * y * x⁻¹ * y⁻¹)) := by group
  rw [hv]
  exact (zpowers z).mul_mem ((zpowers z).inv_mem hu) hmem

theorem comm_C_T (h : Sec11Cnt G z T C Q1 Q2 a x) :
    ∀ g ∈ T, ∀ c ∈ C, g * c * g⁻¹ * c⁻¹ ∈ zpowers z :=
  sec11_comm_C_T h.gen h.z_cent h.C_comm
    (fun q hq c hc => (h.C_Q c hc q hq).symm) h.a_C h.x_C

theorem cover (h : Sec11Cnt G z T C Q1 Q2 a x) :
    ∀ g ∈ T, g ∈ C ⊔ (Q1 ⊔ Q2) ∨
      ∃ w ∈ C ⊔ (Q1 ⊔ Q2), g = a * w ∨ g = x * w ∨ g = a * x * w :=
  sec11_cover_T h.gen le_sup_left le_sup_right h.W_norm h.a_sq h.x_sq h.ax_W

end Sec11Cnt

end CFSG.OddStandard.SmallF3.Omega
