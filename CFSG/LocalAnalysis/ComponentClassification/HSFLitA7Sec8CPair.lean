module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8V
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8TC

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

omit [Finite X] in
theorem inv_conj_of_inv {w a b : X} (hw : w⁻¹ = w) (h : w * a * w⁻¹ = b) : w⁻¹ * a * w = b := by
  rw [hw] at h ⊢
  exact h

structure CPair (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  V : VSide S F T₁
  W : VSide S F T₁
  hyy : W.yi = F.xF * V.yi ∨ W.yi = S.z * (F.xF * V.yi)
  hkk : W.ki = S.z * V.ki
  h4 : S.Sec4 F T₁

theorem z_inv' : S.z⁻¹ = S.z := by rw [inv_eq_iff_mul_eq_one, z_mul_z]

namespace CPair

variable (P : CPair S F T₁)

theorem zk_inv : (S.z * P.V.ki)⁻¹ = S.z * P.V.ki := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two]
  exact S.sq_of_mem_B (mul_mem z_mem_B P.V.hki.mem)

theorem zk_comm {g : X} (hg : g ∈ S.data.T) : S.z * P.V.ki * g = g * (S.z * P.V.ki) :=
  S.central_of_mem_B (mul_mem z_mem_B P.V.hki.mem) hg

theorem yi_mem_T : P.V.yi ∈ S.data.T := P.V.hyi.mem_T

theorem x_mul_yW : F.xF * P.W.yi = S.z * P.V.yi ∨ F.xF * P.W.yi = P.V.yi := by
  have hx : F.xF * F.xF = S.z := by rw [← pow_two, F.xF_sq]
  rcases P.hyy with h | h
  · left; rw [h, ← mul_assoc, hx]
  · right
    rw [h, ← mul_assoc, ← S.central_of_mem_B z_mem_B (xF_mem_T F), mul_assoc S.z, ← mul_assoc F.xF,
      hx, ← mul_assoc, z_mul_z, one_mul]

theorem xyi_mem_E0W : F.xF * P.V.yi ∈ S.E0 P.W.yi P.W.ki := by
  rcases P.hyy with h | h
  · rw [← h]; exact yi_mem_E0 _ _
  · have : F.xF * P.V.yi = S.z * P.W.yi := by rw [h, ← mul_assoc, z_mul_z, one_mul]
    rw [this]; exact mul_mem (z_mem_E0 _ _) (yi_mem_E0 _ _)

theorem n_conj_xyi : P.W.D.v * (F.xF * P.V.yi) * P.W.D.v⁻¹ = F.xF * P.V.yi :=
  v_conj_E0 P.W.D P.xyi_mem_E0W

theorem n_conj_t : P.W.D.v * S.t * P.W.D.v⁻¹ = S.t * (S.z * P.V.ki) := by
  rw [v_conj_t P.W.D, P.hkk]

theorem n_conj_z : P.W.D.v * S.z * P.W.D.v⁻¹ = S.z := v_conj_E0 P.W.D (z_mem_E0 _ _)

theorem w₁_conj_t' : P.V.D.w₁ * S.t * P.V.D.w₁⁻¹ = S.t * (S.z * P.V.ki) := by
  rw [P.V.w₁_conj_t, mul_assoc]

theorem tau_mem_T : P.V.D.w₁⁻¹ * P.W.D.v ∈ S.data.T :=
  inv_mul_mem_T P.h4 (w₁_mem_T₁ P.V.D) (v_mem_T₁ P.W.D) (P.w₁_conj_t'.trans P.n_conj_t.symm)

theorem n_conj_yi : P.W.D.v * P.V.yi * P.W.D.v⁻¹ = S.z * P.V.ki * P.V.yi := by
  have hc := u_comm_v P.W.D
  rw [P.W.u_eq] at hc
  have hfix : P.W.D.v * (S.t * (F.xF * P.W.yi)) * P.W.D.v⁻¹ = S.t * (F.xF * P.W.yi) := by
    rw [← hc]; group
  have hzk := P.zk_inv
  rcases P.x_mul_yW with h | h <;> rw [h] at hfix
  · have e : P.W.D.v * (S.t * (S.z * P.V.yi)) * P.W.D.v⁻¹ = (P.W.D.v * S.t * P.W.D.v⁻¹) *
        (P.W.D.v * S.z * P.W.D.v⁻¹) * (P.W.D.v * P.V.yi * P.W.D.v⁻¹) := by group
    rw [e, P.n_conj_t, P.n_conj_z] at hfix
    calc P.W.D.v * P.V.yi * P.W.D.v⁻¹ =
        (S.t * (S.z * P.V.ki) * S.z)⁻¹ * (S.t * (S.z * P.V.ki) * S.z *
          (P.W.D.v * P.V.yi * P.W.D.v⁻¹)) := by group
      _ = (S.t * (S.z * P.V.ki) * S.z)⁻¹ * (S.t * (S.z * P.V.yi)) := by rw [hfix]
      _ = S.z⁻¹ * P.V.ki⁻¹ * P.V.yi := by group
      _ = S.z * P.V.ki * P.V.yi := by rw [z_inv', P.V.ki_inv]
  · have e : P.W.D.v * (S.t * P.V.yi) * P.W.D.v⁻¹ =
        (P.W.D.v * S.t * P.W.D.v⁻¹) * (P.W.D.v * P.V.yi * P.W.D.v⁻¹) := by group
    rw [e, P.n_conj_t] at hfix
    calc P.W.D.v * P.V.yi * P.W.D.v⁻¹ =
        (S.t * (S.z * P.V.ki))⁻¹ * (S.t * (S.z * P.V.ki) * (P.W.D.v * P.V.yi * P.W.D.v⁻¹)) := by
          group
      _ = (S.t * (S.z * P.V.ki))⁻¹ * (S.t * P.V.yi) := by rw [hfix]
      _ = P.V.ki⁻¹ * S.z⁻¹ * P.V.yi := by group
      _ = S.z * P.V.ki * P.V.yi := by rw [z_inv', P.V.ki_inv, P.V.ki_comm z_mem_T]

theorem tau_conj_yi : (P.V.D.w₁⁻¹ * P.W.D.v) * P.V.yi * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ =
    S.z * P.V.yi := by
  have hw := P.V.w₁_inv
  have h1 := inv_conj_of_inv hw P.V.w₁_conj_z
  have h2 := inv_conj_of_inv hw P.V.w₁_conj_ki
  have h3 := inv_conj_of_inv hw P.V.w₁_conj_yi
  have hky : P.V.ki * P.V.yi = P.V.yi * P.V.ki := P.V.ki_comm P.yi_mem_T
  calc (P.V.D.w₁⁻¹ * P.W.D.v) * P.V.yi * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ =
      P.V.D.w₁⁻¹ * (P.W.D.v * P.V.yi * P.W.D.v⁻¹) * P.V.D.w₁ := by group
    _ = (P.V.D.w₁⁻¹ * S.z * P.V.D.w₁) * (P.V.D.w₁⁻¹ * P.V.ki * P.V.D.w₁) *
        (P.V.D.w₁⁻¹ * P.V.yi * P.V.D.w₁) := by rw [P.n_conj_yi]; group
    _ = S.z * (P.V.ki * P.V.yi) * P.V.ki := by rw [h1, h2, h3]; group
    _ = S.z * P.V.yi := by rw [hky, mul_assoc, mul_assoc, P.V.ki_sq, mul_one]

theorem tau_not_mem_xB : F.xF⁻¹ * (P.V.D.w₁⁻¹ * P.W.D.v) ∉ S.B := by
  intro hb0
  obtain ⟨b, hb, hn⟩ : ∃ b ∈ S.B, P.W.D.v = P.V.D.w₁ * (F.xF * b) := ⟨_, hb0, by group⟩
  have hbT : b ∈ S.data.T := S.B_le_T hb
  have hxyi := refl_x_conj (refl_xmul P.V.hyi)
  have hw1 : P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹ = S.z * (F.xF * P.V.yi) := by
    have h1 := P.n_conj_xyi
    rw [hn] at h1
    have h2 : P.V.D.w₁ * (F.xF * b) * (F.xF * P.V.yi) * (P.V.D.w₁ * (F.xF * b))⁻¹ =
        P.V.D.w₁ * (F.xF * (b * (F.xF * P.V.yi) * b⁻¹) * F.xF⁻¹) * P.V.D.w₁⁻¹ := by group
    rw [h2, S.central_of_mem_B hb P.V.xyi_mem_T, mul_inv_cancel_right, hxyi,
      show P.V.D.w₁ * (S.z * (F.xF * P.V.yi)) * P.V.D.w₁⁻¹ = (P.V.D.w₁ * S.z * P.V.D.w₁⁻¹) *
        (P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹) by group, P.V.w₁_conj_z] at h1
    calc P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹ =
        S.z * (S.z * (P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹)) := by
          rw [← mul_assoc S.z S.z, z_mul_z, one_mul]
      _ = S.z * (F.xF * P.V.yi) := by rw [h1]
  have hw2 : P.V.D.w₁ * F.xF * P.V.D.w₁⁻¹ = S.z * F.xF * P.V.ki := by
    have e : P.V.D.w₁ * F.xF * P.V.D.w₁⁻¹ = (P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹) *
        (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹)⁻¹ := by group
    rw [e, hw1, P.V.w₁_conj_yi, mul_inv_rev, P.V.ki_inv, P.V.yi_inv]
    calc S.z * (F.xF * P.V.yi) * (P.V.ki * P.V.yi) = S.z * F.xF * P.V.yi * (P.V.yi * P.V.ki) := by
          rw [P.V.ki_comm P.yi_mem_T]; group
      _ = S.z * F.xF * (P.V.yi * P.V.yi) * P.V.ki := by group
      _ = S.z * F.xF * P.V.ki := by rw [P.V.yi_mul_yi, mul_one]
  have hx2 : F.xF * F.xF = S.z := by rw [← pow_two, F.xF_sq]
  have hsq : P.W.D.v ^ 2 = P.V.ki * ((P.V.D.w₁ * b * P.V.D.w₁⁻¹) * b) := by
    have hw := P.V.w₁_sq
    rw [pow_two] at hw
    have hb'B : P.V.D.w₁ * b * P.V.D.w₁⁻¹ ∈ S.B := by
      rcases P.V.w₁_conj_B hb with h | h <;> rw [h]
      · exact hb
      · exact mul_mem hb (mul_mem z_mem_B P.V.hki.mem)
    set b' := P.V.D.w₁ * b * P.V.D.w₁⁻¹ with hb'
    calc P.W.D.v ^ 2 = P.V.D.w₁ * F.xF * P.V.D.w₁⁻¹ * b' * (P.V.D.w₁ * P.V.D.w₁) *
          (F.xF * b) := by rw [pow_two, hn, hb']; group
      _ = S.z * F.xF * (P.V.ki * b' * F.xF) * b := by rw [hw2, hw]; group
      _ = S.z * F.xF * (F.xF * (P.V.ki * b')) * b := by
          rw [S.central_of_mem_B (mul_mem P.V.hki.mem hb'B) (xF_mem_T F)]
      _ = S.z * (F.xF * F.xF) * (P.V.ki * b') * b := by group
      _ = P.V.ki * (b' * b) := by rw [hx2, z_mul_z, one_mul, mul_assoc]
  have hbb : b * b = 1 := by rw [← pow_two, S.sq_of_mem_B hb]
  rcases P.V.w₁_conj_B hb with h | h <;> rw [h] at hsq
  ·
    rw [hbb, mul_one] at hsq
    rcases P.W.v_sq_eq with h2 | h2 <;> rw [hsq] at h2
    · exact P.V.hki.ne_one h2
    · rw [P.hkk] at h2
      exact S.z_ne_one (mul_eq_right.mp h2.symm)
  ·
    have e : P.V.ki * (b * (S.z * P.V.ki) * b) = S.z := by
      rw [mul_assoc b, P.zk_comm hbT, ← mul_assoc b b, hbb, one_mul, ← mul_assoc,
        P.V.ki_comm z_mem_T, mul_assoc, P.V.ki_sq, mul_one]
    rw [e] at hsq
    rcases P.W.v_sq_eq with h2 | h2 <;> rw [hsq] at h2
    · exact S.z_ne_one h2
    · rw [P.hkk] at h2
      exact P.V.hki.ne_one (mul_eq_left.mp h2.symm)

theorem tau_mem : (F.xF * P.V.yi)⁻¹ * (P.V.D.w₁⁻¹ * P.W.D.v) ∈ S.B :=
  (mem_xB_of_conj_refl P.V.hyi P.tau_mem_T P.tau_conj_yi).resolve_left P.tau_not_mem_xB

theorem exists_n_eq : ∃ b ∈ S.B, P.W.D.v = P.V.D.w₁ * (F.xF * P.V.yi) * b :=
  ⟨_, P.tau_mem, by group⟩

theorem w₁_conj_xyi : P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹ = F.xF * P.V.yi := by
  obtain ⟨b, hb, hn⟩ := P.exists_n_eq
  have h1 := P.n_conj_xyi
  rw [hn] at h1
  have h2 : P.V.D.w₁ * (F.xF * P.V.yi) * b * (F.xF * P.V.yi) *
      (P.V.D.w₁ * (F.xF * P.V.yi) * b)⁻¹ = P.V.D.w₁ * ((F.xF * P.V.yi) *
        (b * (F.xF * P.V.yi) * b⁻¹) * (F.xF * P.V.yi)⁻¹) * P.V.D.w₁⁻¹ := by group
  rwa [h2, S.central_of_mem_B hb P.V.xyi_mem_T, mul_inv_cancel_right, mul_inv_cancel_right] at h1

theorem w₁_conj_x : P.V.D.w₁ * F.xF * P.V.D.w₁⁻¹ = F.xF * P.V.ki := by
  have e : P.V.D.w₁ * F.xF * P.V.D.w₁⁻¹ = (P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹) *
      (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹)⁻¹ := by group
  rw [e, P.w₁_conj_xyi, P.V.w₁_conj_yi, mul_inv_rev, P.V.ki_inv, P.V.yi_inv,
    P.V.ki_comm P.yi_mem_T]
  calc F.xF * P.V.yi * (P.V.yi * P.V.ki) = F.xF * (P.V.yi * P.V.yi) * P.V.ki := by group
    _ = F.xF * P.V.ki := by rw [P.V.yi_mul_yi, mul_one]

theorem u_conj_w₁ : P.V.D.u * P.V.D.w₁ * P.V.D.u⁻¹ = P.V.D.w₁ * (S.z * P.V.ki) := by
  have h1 : P.V.D.w₁ * P.V.D.u * P.V.D.w₁⁻¹ = P.V.D.u * (S.z * P.V.ki) := by
    rw [P.V.u_eq, show P.V.D.w₁ * (S.t * (F.xF * P.V.yi)) * P.V.D.w₁⁻¹ =
      (P.V.D.w₁ * S.t * P.V.D.w₁⁻¹) * (P.V.D.w₁ * (F.xF * P.V.yi) * P.V.D.w₁⁻¹) by group,
      P.w₁_conj_t', P.w₁_conj_xyi, mul_assoc, P.zk_comm P.V.xyi_mem_T, ← mul_assoc]
  have hu := P.V.u_inv
  have h2 : P.V.D.u⁻¹ * P.V.D.w₁ * P.V.D.u = (S.z * P.V.ki) * P.V.D.w₁ := by
    calc P.V.D.u⁻¹ * P.V.D.w₁ * P.V.D.u =
        P.V.D.u⁻¹ * (P.V.D.w₁ * P.V.D.u * P.V.D.w₁⁻¹) * P.V.D.w₁ := by group
      _ = (S.z * P.V.ki) * P.V.D.w₁ := by rw [h1]; group
  have hc : P.V.D.w₁ * (S.z * P.V.ki) * P.V.D.w₁⁻¹ = S.z * P.V.ki :=
    P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki (mul_mem P.V.z_mem_zk P.V.ki_mem_zk)
  rw [hu] at h2 ⊢
  rw [h2]
  calc S.z * P.V.ki * P.V.D.w₁ = (P.V.D.w₁ * (S.z * P.V.ki) * P.V.D.w₁⁻¹) * P.V.D.w₁ := by
        rw [hc]
    _ = P.V.D.w₁ * (S.z * P.V.ki) := by group

theorem m_conj_t : P.W.D.w₁ * S.t * P.W.D.w₁⁻¹ = S.t * P.V.ki := by
  rw [P.W.w₁_conj_t, P.hkk, mul_assoc, ← mul_assoc S.z, z_mul_z, one_mul]

theorem rho_mem_T : P.V.vN⁻¹ * P.W.D.w₁ ∈ S.data.T :=
  inv_mul_mem_T P.h4 P.V.vN_mem_T₁ (w₁_mem_T₁ P.W.D) (P.V.vN_conj_t.trans P.m_conj_t.symm)

theorem yW_mem_T : P.W.yi ∈ S.data.T := P.W.hyi.mem_T

theorem vN_conj_xyi : P.V.vN * (F.xF * P.V.yi) * P.V.vN⁻¹ = P.V.ki * (F.xF * P.V.yi) := by
  rw [show P.V.vN * (F.xF * P.V.yi) * P.V.vN⁻¹ = (P.V.vN * F.xF * P.V.vN⁻¹) *
    (P.V.vN * P.V.yi * P.V.vN⁻¹) by group, P.V.vN_conj_x, P.V.vN_conj_yi, mul_assoc]

theorem vN_conj_yW : P.V.vN * P.W.yi * P.V.vN⁻¹ = P.V.ki * P.W.yi := by
  rcases P.hyy with h | h <;> rw [h]
  · exact P.vN_conj_xyi
  · rw [show P.V.vN * (S.z * (F.xF * P.V.yi)) * P.V.vN⁻¹ = (P.V.vN * S.z * P.V.vN⁻¹) *
      (P.V.vN * (F.xF * P.V.yi) * P.V.vN⁻¹) by group, P.V.vN_conj_z, P.vN_conj_xyi,
      ← mul_assoc, ← P.V.ki_comm z_mem_T, mul_assoc]

theorem rho_conj_yW : (P.V.vN⁻¹ * P.W.D.w₁) * P.W.yi * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ =
    S.z * P.W.yi := by
  have hv := P.V.vN_inv
  have h1 := inv_conj_of_inv hv P.vN_conj_yW
  have hzk : P.V.vN⁻¹ * (S.z * P.V.ki) * P.V.vN = S.z * P.V.ki :=
    inv_conj_of_inv hv (P.V.vN_conj_of_zk (mul_mem P.V.z_mem_zk P.V.ki_mem_zk))
  have hw := P.W.w₁_conj_yi
  calc (P.V.vN⁻¹ * P.W.D.w₁) * P.W.yi * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ =
      P.V.vN⁻¹ * (P.W.D.w₁ * P.W.yi * P.W.D.w₁⁻¹) * P.V.vN := by group
    _ = (P.V.vN⁻¹ * P.W.yi * P.V.vN) * (P.V.vN⁻¹ * (S.z * P.V.ki) * P.V.vN) := by
        rw [hw, P.hkk]; group
    _ = P.V.ki * P.W.yi * (S.z * P.V.ki) := by rw [h1, hzk]
    _ = P.W.yi * (S.z * (P.V.ki * P.V.ki)) := by
        rw [P.V.ki_comm P.yW_mem_T, mul_assoc, ← mul_assoc P.V.ki, P.V.ki_comm z_mem_T, mul_assoc]
    _ = S.z * P.W.yi := by
        rw [P.V.ki_sq, mul_one, ← S.central_of_mem_B z_mem_B P.yW_mem_T]

theorem rho_not_mem_xB : F.xF⁻¹ * (P.V.vN⁻¹ * P.W.D.w₁) ∉ S.B := by
  intro hb0
  obtain ⟨b, hb, hm⟩ : ∃ b ∈ S.B, P.W.D.w₁ = P.V.vN * (F.xF * b) := ⟨_, hb0, by group⟩
  have hbT := S.B_le_T hb
  have hvv : P.V.vN * P.V.vN = 1 := by rw [← pow_two, P.V.vN_sq]
  have hx2 : F.xF * F.xF = S.z := by rw [← pow_two, F.xF_sq]
  have hsq := P.W.w₁_sq
  rw [pow_two, hm] at hsq
  have hb'B : P.V.vN * b * P.V.vN⁻¹ ∈ S.B := by
    rcases P.V.vN_conj_B hb with h | h <;> rw [h]
    · exact hb
    · exact mul_mem hb P.V.hki.mem
  set b' := P.V.vN * b * P.V.vN⁻¹ with hb'
  have e : P.V.vN * (F.xF * b) * (P.V.vN * (F.xF * b)) = S.z * P.V.ki * (b' * b) := by
    calc P.V.vN * (F.xF * b) * (P.V.vN * (F.xF * b)) =
        (P.V.vN * F.xF * P.V.vN⁻¹) * b' * (P.V.vN * P.V.vN) * (F.xF * b) := by
          rw [hb']; group
      _ = P.V.ki * (F.xF * b' * F.xF) * b := by
          rw [P.V.vN_conj_x, hvv, mul_one]; group
      _ = P.V.ki * ((F.xF * F.xF) * b') * b := by
          rw [mul_assoc F.xF, S.central_of_mem_B hb'B (xF_mem_T F)]; group
      _ = S.z * P.V.ki * (b' * b) := by rw [hx2, ← P.V.ki_comm z_mem_T]; group
  rw [e] at hsq
  have hbb : b * b = 1 := by rw [← pow_two, S.sq_of_mem_B hb]
  rcases P.V.vN_conj_B hb with h | h <;> rw [← hb'] at h <;> rw [h] at hsq
  · rw [hbb, mul_one] at hsq
    apply P.V.hki.not_mem
    have : P.V.ki = S.z := by
      calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, z_mul_z, one_mul]
        _ = S.z := by rw [hsq, mul_one]
    rw [this]; exact mem_sup_left (mem_zpowers _)
  · rw [mul_assoc b, P.V.ki_comm hbT, ← mul_assoc b, hbb, one_mul, mul_assoc, P.V.ki_sq,
      mul_one] at hsq
    exact S.z_ne_one hsq

theorem exists_m_eq : ∃ c ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X),
    P.W.D.w₁ = P.V.vN * (F.xF * P.W.yi) * c := by
  have hb := (mem_xB_of_conj_refl P.W.hyi P.rho_mem_T P.rho_conj_yW).resolve_left
    P.rho_not_mem_xB
  obtain ⟨b, hb, hm⟩ : ∃ b ∈ S.B, P.W.D.w₁ = P.V.vN * (F.xF * P.W.yi) * b :=
    ⟨_, hb, by group⟩
  refine ⟨b, ?_, hm⟩
  have hvv : P.V.vN * P.V.vN = 1 := by rw [← pow_two, P.V.vN_sq]
  have hsq := P.W.w₁_sq
  rw [pow_two, hm] at hsq
  have hxy := refl_xmul_sq P.W.hyi
  rw [pow_two] at hxy
  have hbT := S.B_le_T hb
  have hxyT : F.xF * P.W.yi ∈ S.data.T := mul_mem (xF_mem_T F) P.yW_mem_T
  have h1 : P.V.vN * (F.xF * P.W.yi) * P.V.vN⁻¹ = F.xF * P.W.yi := by
    rw [show P.V.vN * (F.xF * P.W.yi) * P.V.vN⁻¹ = (P.V.vN * F.xF * P.V.vN⁻¹) *
      (P.V.vN * P.W.yi * P.V.vN⁻¹) by group, P.V.vN_conj_x, P.vN_conj_yW,
      show P.V.ki * F.xF * (P.V.ki * P.W.yi) = F.xF * (P.V.ki * P.V.ki) * P.W.yi by
        rw [P.V.ki_comm (xF_mem_T F)]; group, P.V.ki_sq, mul_one]
  have e : P.V.vN * (F.xF * P.W.yi) * b * (P.V.vN * (F.xF * P.W.yi) * b) =
      (P.V.vN * b * P.V.vN⁻¹) * b := by
    calc P.V.vN * (F.xF * P.W.yi) * b * (P.V.vN * (F.xF * P.W.yi) * b) =
        (P.V.vN * (F.xF * P.W.yi) * P.V.vN⁻¹) * (P.V.vN * b * P.V.vN⁻¹) * (P.V.vN * P.V.vN) *
          ((F.xF * P.W.yi) * b) := by group
      _ = (F.xF * P.W.yi) * (P.V.vN * b * P.V.vN⁻¹) * ((F.xF * P.W.yi) * b) := by
          rw [h1, hvv, mul_one]
      _ = (P.V.vN * b * P.V.vN⁻¹) * ((F.xF * P.W.yi) * (F.xF * P.W.yi)) * b := by
          have hb'B : P.V.vN * b * P.V.vN⁻¹ ∈ S.B := by
            rcases P.V.vN_conj_B hb with h | h <;> rw [h]
            · exact hb
            · exact mul_mem hb P.V.hki.mem
          rw [← S.central_of_mem_B hb'B hxyT]; group
      _ = (P.V.vN * b * P.V.vN⁻¹) * b := by rw [hxy, mul_one]
  rw [e] at hsq
  rcases P.V.mem_B_cases hb with h | h
  · exact h
  · exfalso
    rw [P.V.vN_conj_of_t h] at hsq
    have hbb : b * b = 1 := by rw [← pow_two, S.sq_of_mem_B hb]
    rw [mul_assoc, P.V.ki_comm hbT, ← mul_assoc, hbb, one_mul] at hsq
    exact P.V.hki.ne_one hsq

theorem exists_m_eq' : ∃ c ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X),
    P.W.D.w₁ = P.V.vN * P.V.yi * c := by
  obtain ⟨c, hc, hm⟩ := P.exists_m_eq
  rcases P.x_mul_yW with h | h <;> rw [h] at hm
  · refine ⟨S.z * c, mul_mem P.V.z_mem_zk hc, ?_⟩
    rw [hm, S.central_of_mem_B z_mem_B P.yi_mem_T]; group
  · exact ⟨c, hc, hm⟩

theorem w₁_comm_vN : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹ = S.z * P.V.ki := by
  rcases P.V.w₁_comm_C P.V.vN_mem_C with hμ | hμ
  swap
  · exact hμ
  exfalso
  obtain ⟨c, hc, hm⟩ := P.exists_m_eq'
  obtain ⟨b, hb, hn⟩ := P.exists_n_eq
  have hbT := S.B_le_T hb
  have hcB : c ∈ S.B := zk_le_B P.V.hki hc
  have hcT := S.B_le_T hcB
  have hvw : P.V.vN * P.V.D.w₁ * P.V.vN⁻¹ = P.V.D.w₁ := by
    have : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = P.V.vN := by
      calc P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = (P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹) *
          P.V.vN := by group
        _ = P.V.vN := by rw [hμ, one_mul]
    calc P.V.vN * P.V.D.w₁ * P.V.vN⁻¹ =
        (P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹) * P.V.D.w₁ * P.V.vN⁻¹ := by rw [this]
      _ = P.V.D.w₁ := by group
  have hcw : c * P.V.D.w₁ * c⁻¹ = P.V.D.w₁ := by
    have h1 := P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki hc
    calc c * P.V.D.w₁ * c⁻¹ = (P.V.D.w₁ * c * P.V.D.w₁⁻¹) * P.V.D.w₁ * c⁻¹ := by rw [h1]
      _ = P.V.D.w₁ := by group
  have hyw : P.V.yi * P.V.D.w₁ * P.V.yi⁻¹ = P.V.ki * P.V.D.w₁ := by
    have h1 := P.V.w₁_conj_yi
    calc P.V.yi * P.V.D.w₁ * P.V.yi⁻¹ = P.V.yi * (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹)⁻¹ * P.V.D.w₁ := by
          group
      _ = P.V.yi * (P.V.yi * P.V.ki)⁻¹ * P.V.D.w₁ := by rw [h1]
      _ = P.V.ki * P.V.D.w₁ := by
          rw [mul_inv_rev, P.V.ki_inv, P.V.yi_inv, ← mul_assoc, ← P.V.ki_comm P.yi_mem_T,
            mul_assoc P.V.ki, P.V.yi_mul_yi, mul_one]
  have hyx : P.V.yi * (F.xF * P.V.yi * b) * P.V.yi⁻¹ = S.z * (F.xF * P.V.yi) * b := by
    have hinv := P.V.hyi.inv
    rw [xF_inv F] at hinv
    calc P.V.yi * (F.xF * P.V.yi * b) * P.V.yi⁻¹ = (P.V.yi * F.xF * P.V.yi⁻¹) * P.V.yi *
        (P.V.yi * b * P.V.yi⁻¹) := by group
      _ = S.z * (F.xF * P.V.yi) * b := by
          rw [hinv, show P.V.yi * b * P.V.yi⁻¹ = b by
            rw [P.V.hyi.comm_B hb, mul_inv_cancel_right], mul_assoc S.z]
  have hcx : c * (F.xF * P.V.yi * b) * c⁻¹ = F.xF * P.V.yi * b := by
    rw [S.central_of_mem_B hcB (mul_mem P.V.xyi_mem_T hbT), mul_inv_cancel_right]
  have hmn : P.W.D.w₁ * P.W.D.v * P.W.D.w₁⁻¹ * P.W.D.v⁻¹ = 1 ∨
      P.W.D.w₁ * P.W.D.v * P.W.D.w₁⁻¹ * P.W.D.v⁻¹ = P.V.ki := by
    rcases P.W.w₁_comm_C P.W.v_mem_C with h | h
    · exact Or.inl h
    · right; rw [h, P.hkk, ← mul_assoc, z_mul_z, one_mul]
  have hb'B : P.V.vN * b * P.V.vN⁻¹ ∈ S.B := by
    rcases P.V.vN_conj_B hb with h | h <;> rw [h]
    · exact hb
    · exact mul_mem hb P.V.hki.mem
  set b' := P.V.vN * b * P.V.vN⁻¹ with hb'
  have hcomm : P.W.D.w₁ * P.W.D.v * P.W.D.w₁⁻¹ * P.W.D.v⁻¹ = S.z * (b' * b⁻¹) := by
    rw [hm, hn]
    have e1 : P.V.vN * P.V.yi * c * (P.V.D.w₁ * (F.xF * P.V.yi) * b) *
        (P.V.vN * P.V.yi * c)⁻¹ = P.V.vN * ((P.V.yi * c) * P.V.D.w₁ * (P.V.yi * c)⁻¹) *
          ((P.V.yi * c) * (F.xF * P.V.yi * b) * (P.V.yi * c)⁻¹) * P.V.vN⁻¹ := by group
    have e2 : (P.V.yi * c) * P.V.D.w₁ * (P.V.yi * c)⁻¹ = P.V.ki * P.V.D.w₁ := by
      rw [show (P.V.yi * c) * P.V.D.w₁ * (P.V.yi * c)⁻¹ = P.V.yi * (c * P.V.D.w₁ * c⁻¹) *
        P.V.yi⁻¹ by group, hcw, hyw]
    have e3 : (P.V.yi * c) * (F.xF * P.V.yi * b) * (P.V.yi * c)⁻¹ =
        S.z * (F.xF * P.V.yi) * b := by
      rw [show (P.V.yi * c) * (F.xF * P.V.yi * b) * (P.V.yi * c)⁻¹ =
        P.V.yi * (c * (F.xF * P.V.yi * b) * c⁻¹) * P.V.yi⁻¹ by group, hcx, hyx]
    have e4 : P.V.vN * (P.V.ki * P.V.D.w₁ * (S.z * (F.xF * P.V.yi) * b)) * P.V.vN⁻¹ =
        P.V.ki * P.V.D.w₁ * (S.z * (P.V.ki * (F.xF * P.V.yi)) * b') := by
      rw [show P.V.vN * (P.V.ki * P.V.D.w₁ * (S.z * (F.xF * P.V.yi) * b)) * P.V.vN⁻¹ =
        (P.V.vN * P.V.ki * P.V.vN⁻¹) * (P.V.vN * P.V.D.w₁ * P.V.vN⁻¹) *
          ((P.V.vN * S.z * P.V.vN⁻¹) * (P.V.vN * (F.xF * P.V.yi) * P.V.vN⁻¹) * b') by
        rw [hb']; group, P.V.vN_conj_ki, hvw, P.V.vN_conj_z, P.vN_conj_xyi]
    rw [show P.V.vN * P.V.yi * c * (P.V.D.w₁ * (F.xF * P.V.yi) * b) *
      (P.V.vN * P.V.yi * c)⁻¹ * (P.V.D.w₁ * (F.xF * P.V.yi) * b)⁻¹ =
        (P.V.vN * P.V.yi * c * (P.V.D.w₁ * (F.xF * P.V.yi) * b) * (P.V.vN * P.V.yi * c)⁻¹) *
          (P.V.D.w₁ * (F.xF * P.V.yi) * b)⁻¹ by group, e1, e2, e3,
      show P.V.vN * (P.V.ki * P.V.D.w₁) * (S.z * (F.xF * P.V.yi) * b) * P.V.vN⁻¹ =
        P.V.vN * (P.V.ki * P.V.D.w₁ * (S.z * (F.xF * P.V.yi) * b)) * P.V.vN⁻¹ by group, e4]
    have hd : b' * b⁻¹ ∈ S.B := mul_mem hb'B (inv_mem hb)
    have hdzk : S.z * (b' * b⁻¹) ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X) := by
      refine mul_mem P.V.z_mem_zk ?_
      rcases P.V.vN_conj_B hb with h | h <;> rw [← hb'] at h <;> rw [h]
      · rw [mul_inv_cancel]; exact one_mem _
      · rw [mul_assoc, P.V.ki_comm (inv_mem hbT), ← mul_assoc, mul_inv_cancel, one_mul]
        exact P.V.ki_mem_zk
    have hfix := P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki hdzk
    calc P.V.ki * P.V.D.w₁ * (S.z * (P.V.ki * (F.xF * P.V.yi)) * b') *
        (P.V.D.w₁ * (F.xF * P.V.yi) * b)⁻¹ =
        P.V.ki * P.V.D.w₁ * (S.z * P.V.ki * ((F.xF * P.V.yi) * (b' * b⁻¹) *
          (F.xF * P.V.yi)⁻¹)) * P.V.D.w₁⁻¹ := by group
      _ = P.V.ki * P.V.D.w₁ * (P.V.ki * (S.z * (b' * b⁻¹))) * P.V.D.w₁⁻¹ := by
          rw [← S.central_of_mem_B hd P.V.xyi_mem_T, mul_inv_cancel_right,
            ← P.V.ki_comm z_mem_T, mul_assoc P.V.ki S.z]
      _ = P.V.ki * (P.V.D.w₁ * P.V.ki * P.V.D.w₁⁻¹) * (P.V.D.w₁ * (S.z * (b' * b⁻¹)) *
          P.V.D.w₁⁻¹) := by group
      _ = S.z * (b' * b⁻¹) := by rw [P.V.w₁_conj_ki, hfix, ← mul_assoc, P.V.ki_sq, one_mul]
  rw [hcomm] at hmn
  rcases P.V.vN_conj_B hb with h | h <;> rw [← hb'] at h <;> rw [h] at hmn
  · rw [mul_inv_cancel, mul_one] at hmn
    rcases hmn with h1 | h1
    · exact S.z_ne_one h1
    · exact P.V.hki.not_mem (h1 ▸ mem_sup_left (mem_zpowers _))
  · have e : b * P.V.ki * b⁻¹ = P.V.ki := by rw [← P.V.ki_comm hbT, mul_inv_cancel_right]
    rw [e] at hmn
    rcases hmn with h1 | h1
    · apply P.V.hki.not_mem
      have : P.V.ki = S.z := by
        calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, z_mul_z, one_mul]
          _ = S.z := by rw [h1, mul_one]
      rw [this]; exact mem_sup_left (mem_zpowers _)
    · exact S.z_ne_one (mul_eq_right.mp h1)

theorem w₁_conj_vN : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = P.V.vN * (S.z * P.V.ki) := by
  have h := P.w₁_comm_vN
  have hc : P.V.vN * (S.z * P.V.ki) * P.V.vN⁻¹ = S.z * P.V.ki :=
    P.V.vN_conj_of_zk (mul_mem P.V.z_mem_zk P.V.ki_mem_zk)
  calc P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = (P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹) * P.V.vN := by
        group
    _ = (P.V.vN * (S.z * P.V.ki) * P.V.vN⁻¹) * P.V.vN := by rw [h, hc]
    _ = P.V.vN * (S.z * P.V.ki) := by group

end CPair

end Sec8

end CFSG.ComponentClassification.HSFLit
