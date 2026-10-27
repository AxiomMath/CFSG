module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cV3

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem R8_conj_refl_z : ∀ b : ZMod 8, (b = 2 ∨ b = 6) → ∀ u : (ZMod 8)ˣ, (u = 1 ∨ u = -1) →
    ∀ c e : ZMod 8, dbit8 e = 0 →
      aff8 u (2 * c) * aff8 (-1) e * (aff8 u (2 * c))⁻¹ = z8 * aff8 (-1) e →
      aff8 u (2 * c) = aff8 1 b ∨ aff8 u (2 * c) = (aff8 1 b)⁻¹ ∨
        aff8 u (2 * c) = aff8 1 b * aff8 (-1) e ∨ aff8 u (2 * c) = (aff8 1 b)⁻¹ * aff8 (-1) e := by
  decide

theorem xx (S : KDBase A C) : S.x * S.x = S.z := (pow_two S.x).symm

theorem mem_xB_of_conj_refl {r τ : X} (h : IsRefl S r) (hτ : τ ∈ S.TE)
    (hc : τ * r * τ⁻¹ = S.z * r) : S.x⁻¹ * τ ∈ S.B ∨ (S.x * r)⁻¹ * τ ∈ S.B := by
  obtain ⟨s, hs, a, e, -, -, rfl⟩ := exists_eq_of_mem_TE S hτ
  have hb : t ^ a * S.k ^ e ∈ S.B := mul_mem (pow_mem Frame.t_mem_B a) (pow_mem Frame.k_mem_B e)
  have hτ' : s * t ^ a * S.k ^ e = s * (t ^ a * S.k ^ e) := by group
  rw [hτ'] at hc ⊢
  have hsr : s * r * s⁻¹ = S.z * r := by
    have e1 : (t ^ a * S.k ^ e) * r * (t ^ a * S.k ^ e)⁻¹ = r := by
      rw [B_comm_R S hb h.mem, mul_inv_cancel_right]
    rw [show s * (t ^ a * S.k ^ e) * r * (s * (t ^ a * S.k ^ e))⁻¹ =
      s * ((t ^ a * S.k ^ e) * r * (t ^ a * S.k ^ e)⁻¹) * s⁻¹ by group, e1] at hc
    exact hc
  obtain ⟨b₀, hb₀, hx⟩ := ψX_x S
  obtain ⟨e', he', hψr⟩ := h.ψX
  obtain ⟨u, c, hu, hψs⟩ := SD.ψX_mem_R8 (A := A) hs
  have hc8 : aff8 u (2 * c) * aff8 (-1) e' * (aff8 u (2 * c))⁻¹ = z8 * aff8 (-1) e' := by
    rw [hψs, ← hψr, ← SD.ψX_inv hs.1, ← SD.ψX_mul hs.1 h.mem.1,
      ← SD.ψX_mul (mul_mem hs.1 h.mem.1) (inv_mem hs.1), hsr, SD.ψX_mul (z_mem_T S) h.mem.1,
      ψX_z S]
  have hxR := S.x_mem
  have hxT := x_mem_T S
  rcases R8_conj_refl_z b₀ hb₀ u hu c e' he' hc8 with h1 | h1 | h1 | h1 <;> rw [hψs] at h1
  · left
    rw [SD.eq_of_ψX_eq hs hxR (h1.trans hx.symm), ← mul_assoc, inv_mul_cancel, one_mul]
    exact hb
  · left
    have : s = S.x⁻¹ := SD.eq_of_ψX_eq hs (inv_mem hxR)
      (by rw [h1, SD.ψX_inv hxT, hx])
    rw [this, ← mul_assoc, ← mul_inv_rev, xx S, ← z_inv S, inv_inv]
    exact mul_mem Frame.z_mem_B hb
  · right
    have : s = S.x * r := SD.eq_of_ψX_eq hs (mul_mem hxR h.mem)
      (by rw [h1, SD.ψX_mul hxT h.mem.1, hx, hψr])
    rw [this, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hb
  · right
    have : s = S.x⁻¹ * r := SD.eq_of_ψX_eq hs (mul_mem (inv_mem hxR) h.mem)
      (by rw [h1, SD.ψX_mul (inv_mem hxT) h.mem.1, SD.ψX_inv hxT, hx, hψr])
    rw [this, ← mul_assoc, show (S.x * r)⁻¹ * (S.x⁻¹ * r) = r⁻¹ * (S.x⁻¹ * S.x⁻¹) * r by group,
      ← mul_inv_rev, xx S, z_inv S, z_comm_T S (inv_mem h.mem.1), inv_mul_cancel_right]
    exact mul_mem Frame.z_mem_B hb

structure CPair (S : KDBase A C) (T₁ : Subgroup X) where
  V : VSide S T₁
  W : VSide S T₁
  hyy : W.yi = S.x * V.yi
  hkk : W.ki = S.z * V.ki

namespace CPair

variable (P : CPair S T₁)

theorem zk_mem_B : S.z * P.V.ki ∈ S.B := mul_mem Frame.z_mem_B P.V.ki_mem_B

theorem zk_comm {g : X} (hg : g ∈ S.TE) : S.z * P.V.ki * g = g * (S.z * P.V.ki) :=
  central_of_mem_B S P.zk_mem_B hg

theorem x_mul_yW : S.x * P.W.yi = S.z * P.V.yi := by rw [P.hyy, ← mul_assoc, xx S]

theorem x_conj_xyi : S.x * (S.x * P.V.yi) * S.x⁻¹ = S.z * (S.x * P.V.yi) := by
  have h := P.V.hyi.inv
  have h' : P.V.yi * S.x⁻¹ = S.x * P.V.yi := by
    calc P.V.yi * S.x⁻¹ = (P.V.yi * S.x * P.V.yi⁻¹)⁻¹ * P.V.yi := by group
      _ = S.x * P.V.yi := by rw [h, inv_inv]
  rw [mul_assoc, mul_assoc, h', ← mul_assoc, xx S]

theorem n_conj_xyi : P.W.D.v * (S.x * P.V.yi) * P.W.D.v⁻¹ = S.x * P.V.yi := by
  rw [← P.hyy]; exact P.W.v_conj_yi

theorem n_conj_t : P.W.D.v * t * P.W.D.v⁻¹ = t * (S.z * P.V.ki) := by
  rw [P.W.v_conj_t, P.hkk]

theorem n_conj_z : P.W.D.v * S.z * P.W.D.v⁻¹ = S.z := P.W.v_conj_z

theorem n_conj_k : P.W.D.v * S.k * P.W.D.v⁻¹ = S.k := P.W.v_conj_zk P.W.k_mem_zk

theorem w₁_conj_t' : P.V.D.w₁ * t * P.V.D.w₁⁻¹ = t * (S.z * P.V.ki) := by
  rw [P.V.w₁_conj_t, mul_assoc]

theorem tau_mem_TE : P.V.D.w₁⁻¹ * P.W.D.v ∈ S.TE := by
  have hw := P.V.w₁_inv
  refine mem_TE_of_mem_T₁ S P.V.h4 (mul_mem (inv_mem P.V.w₁_mem_T₁) P.W.v_mem_T₁) ?_ ?_
  · have h1 : (P.V.D.w₁⁻¹ * P.W.D.v) * t * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ = t := by
      calc (P.V.D.w₁⁻¹ * P.W.D.v) * t * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ =
          P.V.D.w₁⁻¹ * (P.W.D.v * t * P.W.D.v⁻¹) * P.V.D.w₁ := by group
        _ = P.V.D.w₁⁻¹ * (P.V.D.w₁ * t * P.V.D.w₁⁻¹) * P.V.D.w₁ := by
            rw [P.n_conj_t, P.w₁_conj_t']
        _ = t := by group
    calc (P.V.D.w₁⁻¹ * P.W.D.v) * t = (P.V.D.w₁⁻¹ * P.W.D.v) * t *
        (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ * (P.V.D.w₁⁻¹ * P.W.D.v) := by group
      _ = t * (P.V.D.w₁⁻¹ * P.W.D.v) := by rw [h1]
  · have h1 : (P.V.D.w₁⁻¹ * P.W.D.v) * S.k * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ = S.k := by
      calc (P.V.D.w₁⁻¹ * P.W.D.v) * S.k * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ =
          P.V.D.w₁⁻¹ * (P.W.D.v * S.k * P.W.D.v⁻¹) * P.V.D.w₁ := by group
        _ = P.V.D.w₁ * S.k * P.V.D.w₁⁻¹ := by rw [P.n_conj_k, hw]
        _ = S.k := P.V.w₁_conj_k
    calc (P.V.D.w₁⁻¹ * P.W.D.v) * S.k = (P.V.D.w₁⁻¹ * P.W.D.v) * S.k *
        (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ * (P.V.D.w₁⁻¹ * P.W.D.v) := by group
      _ = S.k * (P.V.D.w₁⁻¹ * P.W.D.v) := by rw [h1]

theorem n_conj_yi : P.W.D.v * P.V.yi * P.W.D.v⁻¹ = S.z * P.V.ki * P.V.yi := by
  have hc := P.W.u_comm_v
  rw [P.W.u_eq', P.x_mul_yW] at hc
  have hfix : P.W.D.v * (t * (S.z * P.V.yi)) * P.W.D.v⁻¹ = t * (S.z * P.V.yi) := by
    rw [← hc]; group
  have e : P.W.D.v * (t * (S.z * P.V.yi)) * P.W.D.v⁻¹ = (P.W.D.v * t * P.W.D.v⁻¹) *
      (P.W.D.v * S.z * P.W.D.v⁻¹) * (P.W.D.v * P.V.yi * P.W.D.v⁻¹) := by group
  rw [e, P.n_conj_t, P.n_conj_z] at hfix
  calc P.W.D.v * P.V.yi * P.W.D.v⁻¹ =
      (t * (S.z * P.V.ki) * S.z)⁻¹ * (t * (S.z * P.V.ki) * S.z *
        (P.W.D.v * P.V.yi * P.W.D.v⁻¹)) := by group
    _ = (t * (S.z * P.V.ki) * S.z)⁻¹ * (t * (S.z * P.V.yi)) := by rw [hfix]
    _ = S.z⁻¹ * P.V.ki⁻¹ * P.V.yi := by group
    _ = S.z * P.V.ki * P.V.yi := by rw [z_inv S, P.V.ki_inv]

theorem tau_conj_yi : (P.V.D.w₁⁻¹ * P.W.D.v) * P.V.yi * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ =
    S.z * P.V.yi := by
  have hw := P.V.w₁_inv
  have h1 : P.V.D.w₁⁻¹ * S.z * P.V.D.w₁ = S.z := by
    rw [hw]; nth_rewrite 2 [← hw]; exact P.V.w₁_conj_z
  have h2 : P.V.D.w₁⁻¹ * P.V.ki * P.V.D.w₁ = P.V.ki := by
    rw [hw]; nth_rewrite 2 [← hw]; exact P.V.w₁_conj_ki
  have h3 : P.V.D.w₁⁻¹ * P.V.yi * P.V.D.w₁ = P.V.yi * P.V.ki := by
    rw [hw]; nth_rewrite 2 [← hw]; exact P.V.w₁_conj_yi
  have hky : P.V.ki * P.V.yi = P.V.yi * P.V.ki := P.V.ki_comm P.V.yi_mem_TE
  calc (P.V.D.w₁⁻¹ * P.W.D.v) * P.V.yi * (P.V.D.w₁⁻¹ * P.W.D.v)⁻¹ =
      P.V.D.w₁⁻¹ * (P.W.D.v * P.V.yi * P.W.D.v⁻¹) * P.V.D.w₁ := by group
    _ = (P.V.D.w₁⁻¹ * S.z * P.V.D.w₁) * (P.V.D.w₁⁻¹ * P.V.ki * P.V.D.w₁) *
        (P.V.D.w₁⁻¹ * P.V.yi * P.V.D.w₁) := by rw [P.n_conj_yi]; group
    _ = S.z * (P.V.ki * P.V.yi) * P.V.ki := by rw [h1, h2, h3]; group
    _ = S.z * P.V.yi := by rw [hky, mul_assoc, mul_assoc, P.V.ki_sq, mul_one]

theorem tau_not_mem_xB : S.x⁻¹ * (P.V.D.w₁⁻¹ * P.W.D.v) ∉ S.B := by
  intro hb0
  obtain ⟨b, hb, hn⟩ : ∃ b ∈ S.B, P.W.D.v = P.V.D.w₁ * (S.x * b) := ⟨_, hb0, by group⟩
  have hbTE : b ∈ S.TE := B_le_TE S hb
  have hw1 : P.V.D.w₁ * (S.x * P.V.yi) * P.V.D.w₁⁻¹ = S.z * (S.x * P.V.yi) := by
    have h1 := P.n_conj_xyi
    rw [hn] at h1
    have h2 : P.V.D.w₁ * (S.x * b) * (S.x * P.V.yi) * (P.V.D.w₁ * (S.x * b))⁻¹ =
        P.V.D.w₁ * (S.x * (b * (S.x * P.V.yi) * b⁻¹) * S.x⁻¹) * P.V.D.w₁⁻¹ := by group
    rw [h2, central_of_mem_B S hb P.V.xyi_mem_TE, mul_inv_cancel_right, P.x_conj_xyi,
      show P.V.D.w₁ * (S.z * (S.x * P.V.yi)) * P.V.D.w₁⁻¹ = (P.V.D.w₁ * S.z * P.V.D.w₁⁻¹) *
        (P.V.D.w₁ * (S.x * P.V.yi) * P.V.D.w₁⁻¹) by group, P.V.w₁_conj_z] at h1
    calc P.V.D.w₁ * (S.x * P.V.yi) * P.V.D.w₁⁻¹ =
        S.z * (S.z * (P.V.D.w₁ * (S.x * P.V.yi) * P.V.D.w₁⁻¹)) := by
          rw [← mul_assoc S.z S.z, zz S, one_mul]
      _ = S.z * (S.x * P.V.yi) := by rw [h1]
  have hw2 : P.V.D.w₁ * S.x * P.V.D.w₁⁻¹ = S.z * S.x * P.V.ki := by
    have e : P.V.D.w₁ * S.x * P.V.D.w₁⁻¹ = (P.V.D.w₁ * (S.x * P.V.yi) * P.V.D.w₁⁻¹) *
        (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹)⁻¹ := by group
    rw [e, hw1, P.V.w₁_conj_yi, mul_inv_rev, P.V.ki_inv, P.V.yi_inv]
    calc S.z * (S.x * P.V.yi) * (P.V.ki * P.V.yi) = S.z * S.x * P.V.yi * (P.V.yi * P.V.ki) := by
          rw [P.V.ki_comm P.V.yi_mem_TE]; group
      _ = S.z * S.x * (P.V.yi * P.V.yi) * P.V.ki := by group
      _ = S.z * S.x * P.V.ki := by rw [P.V.yi_sq, mul_one]
  have hsq : P.W.D.v ^ 2 = P.V.ki * ((P.V.D.w₁ * b * P.V.D.w₁⁻¹) * b) := by
    have hw := P.V.w₁_mul
    have hb'B : P.V.D.w₁ * b * P.V.D.w₁⁻¹ ∈ S.B := by
      rcases P.V.w₁_conj_B hb with h | h <;> rw [h]
      · exact hb
      · exact mul_mem hb P.zk_mem_B
    set b' := P.V.D.w₁ * b * P.V.D.w₁⁻¹ with hb'
    calc P.W.D.v ^ 2 = P.V.D.w₁ * S.x * P.V.D.w₁⁻¹ * b' * (P.V.D.w₁ * P.V.D.w₁) *
          (S.x * b) := by rw [pow_two, hn, hb']; group
      _ = S.z * S.x * (P.V.ki * b' * S.x) * b := by rw [hw2, hw]; group
      _ = S.z * S.x * (S.x * (P.V.ki * b')) * b := by
          rw [central_of_mem_B S (mul_mem P.V.ki_mem_B hb'B) (R_le_TE S S.x_mem)]
      _ = S.z * (S.x * S.x) * (P.V.ki * b') * b := by group
      _ = P.V.ki * (b' * b) := by rw [xx S, zz S, one_mul, mul_assoc]
  have hbb : b * b = 1 := by rw [← pow_two, sq_of_mem_B S hb]
  rcases P.V.w₁_conj_B hb with h | h <;> rw [h] at hsq
  ·
    rw [hbb, mul_one] at hsq
    rcases P.W.v_sq_eq with h2 | h2 <;> rw [hsq] at h2
    · exact P.V.ki_ne_one h2
    · rw [P.hkk] at h2
      exact z_ne_one S (mul_eq_right.mp h2.symm)
  ·
    have e : P.V.ki * (b * (S.z * P.V.ki) * b) = S.z := by
      rw [mul_assoc b, P.zk_comm hbTE, ← mul_assoc b b, hbb, one_mul, ← mul_assoc,
        P.V.ki_comm (R_le_TE S (z_mem_R S)), mul_assoc, P.V.ki_sq, mul_one]
    rw [e] at hsq
    rcases P.W.v_sq_eq with h2 | h2 <;> rw [hsq] at h2
    · exact z_ne_one S h2
    · rw [P.hkk] at h2
      exact P.V.ki_ne_one (mul_eq_left.mp h2.symm)

theorem tau_mem : (S.x * P.V.yi)⁻¹ * (P.V.D.w₁⁻¹ * P.W.D.v) ∈ S.B :=
  (mem_xB_of_conj_refl P.V.hyi P.tau_mem_TE P.tau_conj_yi).resolve_left P.tau_not_mem_xB

theorem exists_n_eq : ∃ b ∈ S.B, P.W.D.v = P.V.D.w₁ * (S.x * P.V.yi) * b :=
  ⟨_, P.tau_mem, by group⟩

theorem w₁_conj_xyi : P.V.D.w₁ * (S.x * P.V.yi) * P.V.D.w₁⁻¹ = S.x * P.V.yi := by
  obtain ⟨b, hb, hn⟩ := P.exists_n_eq
  have h1 := P.n_conj_xyi
  rw [hn] at h1
  have h2 : P.V.D.w₁ * (S.x * P.V.yi) * b * (S.x * P.V.yi) *
      (P.V.D.w₁ * (S.x * P.V.yi) * b)⁻¹ = P.V.D.w₁ * ((S.x * P.V.yi) *
        (b * (S.x * P.V.yi) * b⁻¹) * (S.x * P.V.yi)⁻¹) * P.V.D.w₁⁻¹ := by group
  rwa [h2, central_of_mem_B S hb P.V.xyi_mem_TE, mul_inv_cancel_right,
    mul_inv_cancel_right] at h1

theorem u_conj_w₁ : P.V.D.u * P.V.D.w₁ * P.V.D.u⁻¹ = P.V.D.w₁ * (S.z * P.V.ki) := by
  have h1 : P.V.D.w₁ * P.V.D.u * P.V.D.w₁⁻¹ = P.V.D.u * (S.z * P.V.ki) := by
    rw [P.V.u_eq', show P.V.D.w₁ * (t * (S.x * P.V.yi)) * P.V.D.w₁⁻¹ =
      (P.V.D.w₁ * t * P.V.D.w₁⁻¹) * (P.V.D.w₁ * (S.x * P.V.yi) * P.V.D.w₁⁻¹) by group,
      P.w₁_conj_t', P.w₁_conj_xyi, mul_assoc, P.zk_comm P.V.xyi_mem_TE, ← mul_assoc]
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

end CPair

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
