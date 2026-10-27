module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cSplit

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

structure VSide (S : KDBase A C) (T₁ : Subgroup X) where
  yi : X
  ki : X
  ui : X
  hyi : IsRefl S yi
  hki : ki = S.k ∨ ki = S.z * S.k
  hui : ui = S.x * yi
  D : S.Sec6 T₁ yi ki ui
  hq : D.q0 = .extraspecial
  hu : D.u = t * ui
  h4 : S.Sec4 T₁

namespace VSide

variable (V : VSide S T₁)

abbrev F : Frame S := frameOf V.hyi V.hki

theorem act : S.ActHolds V.yi V.ki V.D.v V.D.w₁ V.D.w₂ .two := act_two_of_extra V.D V.hq

theorem ki_sq : V.ki * V.ki = 1 := V.F.kF_kF

theorem ki_sq' : V.ki ^ 2 = 1 := V.F.kF_sq

theorem ki_inv : V.ki⁻¹ = V.ki := V.F.kF_inv

theorem ki_mem_T : V.ki ∈ A.T := V.F.kF_mem_T

theorem ki_mem_B : V.ki ∈ S.B := V.F.kF_mem_B

theorem ki_ne_one : V.ki ≠ 1 := V.F.kF_ne_one

theorem ki_ne_z : V.ki ≠ S.z := fun h => V.F.kF_not_mem_z (h ▸ mem_zpowers _)

theorem ki_comm {g : X} (hg : g ∈ S.TE) : V.ki * g = g * V.ki :=
  central_of_mem_B S V.ki_mem_B hg

theorem yi_sq : V.yi * V.yi = 1 := V.F.yF_yF

theorem yi_inv : V.yi⁻¹ = V.yi := V.F.yF_inv'

theorem yi_mem_R : V.yi ∈ A.R := V.hyi.mem

theorem yi_mem_T : V.yi ∈ A.T := V.hyi.mem.1

theorem yi_mem_TE : V.yi ∈ S.TE := R_le_TE S V.yi_mem_R

theorem z_mem_E0 : S.z ∈ S.E0 V.yi V.ki := V.F.z_mem_E0

theorem yi_mem_E0 : V.yi ∈ S.E0 V.yi V.ki := V.F.yF_mem_E0

theorem ki_mem_E0 : V.ki ∈ S.E0 V.yi V.ki := V.F.kF_mem_E0

theorem E0_le_E : S.E0 V.yi V.ki ≤ S.E V.yi := V.F.E0_le_E

theorem xyi_mem_TE : S.x * V.yi ∈ S.TE := R_le_TE S (mul_mem S.x_mem V.hyi.mem)

theorem xyi_sq : (S.x * V.yi) * (S.x * V.yi) = 1 := by rw [← pow_two]; exact V.F.xyF_sq

theorem x_conj_yi : S.x * V.yi * S.x⁻¹ = S.z * V.yi := V.F.xF_conj_yF

theorem u_eq' : V.D.u = t * (S.x * V.yi) := by rw [V.hu, V.hui]

theorem u_mem_TE : V.D.u ∈ S.TE := by
  rw [V.u_eq']; exact mul_mem (B_le_TE S Frame.t_mem_B) V.xyi_mem_TE

theorem u_mem_T : V.D.u ∈ A.T := TE_le_T S V.u_mem_TE

theorem u_sq : V.D.u * V.D.u = 1 := by
  rw [V.u_eq']
  have h1 : t * (S.x * V.yi) = (S.x * V.yi) * t := (A.commute_t (TE_le_T S V.xyi_mem_TE)).symm
  calc t * (S.x * V.yi) * (t * (S.x * V.yi)) = t * ((S.x * V.yi) * t) * (S.x * V.yi) := by
        group
    _ = (t * t) * ((S.x * V.yi) * (S.x * V.yi)) := by rw [← h1]; group
    _ = 1 := by rw [tt (A := A), V.xyi_sq, one_mul]

theorem u_inv : V.D.u⁻¹ = V.D.u := inv_eq_of_mul_eq_one_right V.u_sq

theorem u_conj_B {b : X} (hb : b ∈ S.B) : V.D.u * b * V.D.u⁻¹ = b := by
  rw [← central_of_mem_B S hb V.u_mem_TE, mul_inv_cancel_right]

theorem B_u {b : X} (hb : b ∈ S.B) : b * V.D.u = V.D.u * b := central_of_mem_B S hb V.u_mem_TE

theorem u_conj_t : V.D.u * t * V.D.u⁻¹ = t := V.u_conj_B Frame.t_mem_B

theorem u_conj_z : V.D.u * S.z * V.D.u⁻¹ = S.z := V.u_conj_B Frame.z_mem_B

theorem u_conj_ki : V.D.u * V.ki * V.D.u⁻¹ = V.ki := V.u_conj_B V.ki_mem_B

theorem u_conj_yi : V.D.u * V.yi * V.D.u⁻¹ = S.z * V.yi := by
  rw [V.u_eq']
  have hzy : S.z * V.yi ∈ A.T := mul_mem (z_mem_T S) V.yi_mem_T
  calc t * (S.x * V.yi) * V.yi * (t * (S.x * V.yi))⁻¹ =
      t * (S.x * (V.yi * V.yi * V.yi⁻¹) * S.x⁻¹) * t⁻¹ := by group
    _ = t * (S.z * V.yi) * t⁻¹ := by rw [mul_inv_cancel_right, V.x_conj_yi]
    _ = S.z * V.yi := by rw [← A.commute_t hzy, mul_inv_cancel_right]

theorem u_comm_v : V.D.u * V.D.v = V.D.v * V.D.u :=
  V.D.u_comm_C V.D.v (V.D.C_eq ▸ subset_closure (by simp))

theorem u_mem_S₁ : V.D.u ∈ V.D.S₁ := by
  rw [V.D.S₁_eq]; exact mem_sup_right (mem_zpowers _)

theorem w₂_mem_S₁ : V.D.w₂ ∈ V.D.S₁ := KD7.w₂_mem_S₁ (F := V.F) V.D

theorem v_mem_S₁ : V.D.v ∈ V.D.S₁ := KD7.v_mem_S₁ (F := V.F) V.D

theorem w₁_mem_S₁ : V.D.w₁ ∈ V.D.S₁ := KD7.w₁_mem_S₁ (F := V.F) V.D

theorem E_le_S₁ : S.E V.yi ≤ V.D.S₁ := by
  rw [V.D.S₁_eq]
  exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))

theorem t_mem_S₁ : t ∈ V.D.S₁ := V.E_le_S₁ (Frame.t_mem_E _)

theorem v_mem_T₁ : V.D.v ∈ T₁ :=
  V.D.T₁_eq.symm.le (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem w₁_mem_T₁ : V.D.w₁ ∈ T₁ := V.D.T₁_eq.symm.le (mem_sup_right (mem_zpowers _))

include V in
theorem T_le_T₁ : A.T ≤ T₁ := V.h4.le

include V in
theorem t_mem_T₁ : t ∈ T₁ := V.T_le_T₁ A.t_mem_T

theorem v_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.v * e * V.D.v⁻¹ = e :=
  V.act.1 e he

theorem v_conj_t : V.D.v * t * V.D.v⁻¹ = t * V.ki := V.act.2.1

theorem v_conj_yi : V.D.v * V.yi * V.D.v⁻¹ = V.yi := V.v_conj_E0 V.yi_mem_E0

theorem v_conj_z : V.D.v * S.z * V.D.v⁻¹ = S.z := V.v_conj_E0 V.z_mem_E0

theorem v_conj_x : V.D.v * S.x * V.D.v⁻¹ = V.ki * S.x := by
  have hc := V.u_comm_v
  rw [V.u_eq'] at hc
  have h1 : V.D.v * (t * (S.x * V.yi)) * V.D.v⁻¹ = t * (S.x * V.yi) := by
    rw [← hc]; group
  have h2 : V.D.v * (t * (S.x * V.yi)) * V.D.v⁻¹ =
      (V.D.v * t * V.D.v⁻¹) * (V.D.v * S.x * V.D.v⁻¹) * (V.D.v * V.yi * V.D.v⁻¹) := by
    group
  rw [h2, V.v_conj_t, V.v_conj_yi] at h1
  have h3 : t * V.ki * (V.D.v * S.x * V.D.v⁻¹) = t * S.x := mul_right_cancel
    (by rw [h1, mul_assoc])
  calc V.D.v * S.x * V.D.v⁻¹ = V.ki * (t⁻¹ * (t * V.ki * (V.D.v * S.x * V.D.v⁻¹))) := by
        rw [show t⁻¹ * (t * V.ki * (V.D.v * S.x * V.D.v⁻¹)) =
          V.ki * (V.D.v * S.x * V.D.v⁻¹) by group, ← mul_assoc, V.ki_sq, one_mul]
    _ = V.ki * S.x := by rw [h3]; group

theorem eq_of_mem_zk {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    c = 1 ∨ c = S.z ∨ c = V.ki ∨ c = S.z * V.ki := by
  rcases Sec7.mem_or_of_mem_sup (elemAbelianTwo_z S) V.ki_sq'
    (fun a ha => comm_zpowers_z S V.ki_mem_T ha) hc with h | h
  · rcases eq_one_or_eq_of_mem_zpowers (z_sq S) h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases eq_one_or_eq_of_mem_zpowers (z_sq S) h with h | h
    · right; right; left
      calc c = c * V.ki * V.ki := by rw [mul_assoc, V.ki_sq, mul_one]
        _ = V.ki := by rw [h, one_mul]
    · right; right; right
      calc c = c * V.ki * V.ki := by rw [mul_assoc, V.ki_sq, mul_one]
        _ = S.z * V.ki := by rw [h]

theorem z_mem_zk : S.z ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) :=
  mem_sup_left (mem_zpowers _)

theorem ki_mem_zk : V.ki ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) :=
  mem_sup_right (mem_zpowers _)

theorem zk_le_E0 : (zpowers S.z ⊔ zpowers V.ki : Subgroup X) ≤ S.E0 V.yi V.ki := V.F.zk_le_E0

theorem zk_le_B : (zpowers S.z ⊔ zpowers V.ki : Subgroup X) ≤ S.B :=
  sup_le (zpowers_le.mpr Frame.z_mem_B) (zpowers_le.mpr V.ki_mem_B)

theorem conj_zk_of_fix {g : X} (hz : g * S.z * g⁻¹ = S.z) (hk : g * V.ki * g⁻¹ = V.ki) {c : X}
    (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) : g * c * g⁻¹ = c := by
  rcases V.eq_of_mem_zk hc with rfl | rfl | rfl | rfl
  · group
  · exact hz
  · exact hk
  · rw [show g * (S.z * V.ki) * g⁻¹ = (g * S.z * g⁻¹) * (g * V.ki * g⁻¹) by group, hz, hk]

theorem t_not_mem_zk : t ∉ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := fun h =>
  V.F.t_not_mem_E0 (V.zk_le_E0 h)

theorem k_mem_zk : S.k ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  rcases V.F.k_eq with h | h <;> rw [h]
  · exact mem_sup_right (mem_zpowers _)
  · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem B_eq' : S.B = (zpowers S.z ⊔ zpowers V.ki) ⊔ zpowers t := by
  apply le_antisymm
  · rw [B_eq]
    exact sup_le (sup_le (zpowers_le.mpr (mem_sup_left (mem_sup_left (mem_zpowers _))))
      (zpowers_le.mpr (mem_sup_right (mem_zpowers _)))) (zpowers_le.mpr (mem_sup_left V.k_mem_zk))
  · exact sup_le V.zk_le_B (zpowers_le.mpr Frame.t_mem_B)

theorem mem_B_cases {b : X} (hb : b ∈ S.B) :
    b ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) ∨
      b * t ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  rw [V.B_eq'] at hb
  exact Sec7.mem_or_of_mem_sup V.F.elemAbelianTwo_zk (SD.t_sq (A := A))
    (fun a ha => (B_comm_B S Frame.t_mem_B (V.zk_le_B ha))) hb

theorem yi_not_mem_B : V.yi ∉ S.B := by
  intro h
  have hyL : V.yi ∈ L := V.hyi.mem.2.1
  have htL := t_not_mem_L (A := A)
  have htk := V.F.t_kF_not_mem_L
  rcases V.mem_B_cases h with h' | h'
  · exact V.F.yF_not_mem_zk h'
  · have htc : t * V.yi = V.yi * t := (A.commute_t V.yi_mem_T).symm
    rcases V.eq_of_mem_zk h' with h1 | h1 | h1 | h1
    · apply htL
      rw [show t = V.yi⁻¹ * (V.yi * t) by group, h1, mul_one]
      exact inv_mem hyL
    · apply htL
      rw [show t = V.yi⁻¹ * (V.yi * t) by group, h1]
      exact mul_mem (inv_mem hyL) (z_mem_L S)
    · apply htk
      rw [show V.F.kF = V.ki from rfl, ← h1, ← mul_assoc, htc, mul_assoc, tt (A := A), mul_one]
      exact hyL
    · apply htk
      have h2 : V.ki = S.z * (V.yi * t) := by
        rw [h1, ← mul_assoc, zz S, one_mul]
      rw [show V.F.kF = V.ki from rfl, h2, show t * (S.z * (V.yi * t)) = S.z * (t * V.yi * t) by
        rw [← mul_assoc, ← mul_assoc, (A.commute_t (z_mem_T S)).symm]; group, htc, mul_assoc,
        tt (A := A), mul_one]
      exact mul_mem (z_mem_L S) hyL

theorem mem_E0_of_comm_v {e : X} (he : e ∈ S.E V.yi) (hv : V.D.v * e * V.D.v⁻¹ = e) :
    e ∈ S.E0 V.yi V.ki := by
  rcases V.F.mem_E0_or he with h | h
  · exact h
  · exfalso
    have h1 := V.v_conj_E0 h
    have h2 : V.D.v * (e * t) * V.D.v⁻¹ = e * (t * V.ki) := by
      rw [show V.D.v * (e * t) * V.D.v⁻¹ = (V.D.v * e * V.D.v⁻¹) * (V.D.v * t * V.D.v⁻¹)
        by group, hv, V.v_conj_t]
    rw [h1, ← mul_assoc] at h2
    exact V.ki_ne_one (mul_eq_left.mp h2.symm)

theorem conj_mem_E0 {n : X} (hn : n ∈ normalizer (S.E V.yi : Set X)) {e : X}
    (he : e ∈ S.E0 V.yi V.ki) : n * e * n⁻¹ ∈ S.E0 V.yi V.ki := by
  have heE : e ∈ S.E V.yi := V.E0_le_E he
  refine V.mem_E0_of_comm_v (Sec7.conj_mem_of_mem_normalizer hn heE) ?_
  have hc := V.D.v_central n⁻¹ (inv_mem hn)
  rw [inv_inv] at hc
  set c := n⁻¹ * V.D.v * n * V.D.v⁻¹ with hcdef
  have hce : c * e = e * c := (mem_centralizer_iff.mp hc e heE).symm
  have hv : n⁻¹ * V.D.v * n = c * V.D.v := by rw [hcdef]; group
  calc V.D.v * (n * e * n⁻¹) * V.D.v⁻¹ = n * (n⁻¹ * V.D.v * n) * e * (n⁻¹ * V.D.v * n)⁻¹ * n⁻¹ := by
        group
    _ = n * (c * (V.D.v * e * V.D.v⁻¹) * c⁻¹) * n⁻¹ := by rw [hv]; group
    _ = n * e * n⁻¹ := by rw [V.v_conj_E0 he, hce]; group

end VSide

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
