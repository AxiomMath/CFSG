module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abMixV

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

structure ISide (S : KDBase A C) (T₁ : Subgroup X) where
  yi : X
  ki : X
  ui : X
  hyi : IsRefl S yi
  hki : ki = S.k ∨ ki = S.z * S.k
  hui : ui = S.x * yi
  D : S.Sec6 T₁ yi ki ui
  hq : D.q0 = .elem ∨ D.q0 = .homocyclic
  hu : D.u = ui
  h4 : S.Sec4 T₁

namespace ISide

variable (V : ISide S T₁)

abbrev F : Frame S := frameOf V.hyi V.hki

theorem hact : V.D.act = .one := act_one_of_abelian (F := V.F) V.D V.hq

theorem act : (∀ e ∈ S.E0 V.yi V.ki, V.D.v * e * V.D.v⁻¹ = e ∧ V.D.w₁ * e * V.D.w₁⁻¹ = e ∧
      V.D.w₂ * e * V.D.w₂⁻¹ = e) ∧ V.D.v * t * V.D.v⁻¹ = t * V.ki ∧
    V.D.w₁ * t * V.D.w₁⁻¹ = t * S.z ∧ V.D.w₂ * t * V.D.w₂⁻¹ = t * V.yi := by
  have h := V.D.act_holds
  rw [V.hact] at h
  exact h

theorem ki_sq : V.ki * V.ki = 1 := V.F.kF_kF

theorem ki_sq' : V.ki ^ 2 = 1 := V.F.kF_sq

theorem ki_mem_T : V.ki ∈ A.T := V.F.kF_mem_T

theorem ki_mem_B : V.ki ∈ S.B := V.F.kF_mem_B

theorem ki_ne_one : V.ki ≠ 1 := V.F.kF_ne_one

theorem yi_sq : V.yi * V.yi = 1 := V.F.yF_yF

theorem yi_mem_T : V.yi ∈ A.T := V.hyi.mem.1

theorem z_mem_E0 : S.z ∈ S.E0 V.yi V.ki := V.F.z_mem_E0

theorem yi_mem_E0 : V.yi ∈ S.E0 V.yi V.ki := V.F.yF_mem_E0

theorem ki_mem_E0 : V.ki ∈ S.E0 V.yi V.ki := V.F.kF_mem_E0

theorem E0_le_E : S.E0 V.yi V.ki ≤ S.E V.yi := V.F.E0_le_E

theorem E0_comm {a b : X} (ha : a ∈ S.E0 V.yi V.ki) (hb : b ∈ S.E0 V.yi V.ki) :
    a * b = b * a := V.F.comm_E0 ha hb

theorem t_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : t * e = e * t := V.F.t_comm_E0 he

theorem ui_mem_R : V.ui ∈ A.R := by rw [V.hui]; exact mul_mem S.x_mem V.hyi.mem

theorem u_mem_R : V.D.u ∈ A.R := by rw [V.hu]; exact V.ui_mem_R

theorem u_mem_T : V.D.u ∈ A.T := V.u_mem_R.1

theorem u_sq : V.D.u * V.D.u = 1 := by rw [V.hu, V.hui, ← pow_two]; exact V.F.xyF_sq

theorem u_inv : V.D.u⁻¹ = V.D.u := inv_eq_of_mul_eq_one_right V.u_sq

theorem u_conj_yi : V.D.u * V.yi * V.D.u⁻¹ = S.z * V.yi := by
  rw [V.hu, V.hui, show S.x * V.yi * V.yi * (S.x * V.yi)⁻¹ = S.x * (V.yi * V.yi * V.yi⁻¹) *
    S.x⁻¹ by group, mul_inv_cancel_right]
  exact V.F.xF_conj_yF

theorem u_conj_B {b : X} (hb : b ∈ S.B) : V.D.u * b * V.D.u⁻¹ = b := by
  rw [← B_comm_R S hb V.u_mem_R, mul_inv_cancel_right]

theorem u_conj_t : V.D.u * t * V.D.u⁻¹ = t := V.u_conj_B Frame.t_mem_B

theorem u_conj_z : V.D.u * S.z * V.D.u⁻¹ = S.z := V.u_conj_B Frame.z_mem_B

theorem u_conj_ki : V.D.u * V.ki * V.D.u⁻¹ = V.ki := V.u_conj_B V.ki_mem_B

theorem u_mem_S₁ : V.D.u ∈ V.D.S₁ := by
  rw [V.D.S₁_eq]; exact mem_sup_right (mem_zpowers _)

theorem w₂_mem_S₁ : V.D.w₂ ∈ V.D.S₁ := KD7.w₂_mem_S₁ (F := V.F) V.D

theorem v_mem_S₁ : V.D.v ∈ V.D.S₁ := KD7.v_mem_S₁ (F := V.F) V.D

theorem v_mem_T₁ : V.D.v ∈ T₁ :=
  V.D.T₁_eq.symm.le (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem w₁_mem_T₁ : V.D.w₁ ∈ T₁ := V.D.T₁_eq.symm.le (mem_sup_right (mem_zpowers _))

include V in
theorem T_le_T₁ : A.T ≤ T₁ := V.h4.le

include V in
theorem t_mem_T₁ : t ∈ T₁ := V.T_le_T₁ A.t_mem_T

theorem v_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.v * e * V.D.v⁻¹ = e :=
  (V.act.1 e he).1

theorem v_conj_t : V.D.v * t * V.D.v⁻¹ = t * V.ki := V.act.2.1

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

theorem v_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.v * e = e * V.D.v := by
  have h := V.v_conj_E0 he
  calc V.D.v * e = V.D.v * e * V.D.v⁻¹ * V.D.v := by group
    _ = e * V.D.v := by rw [h]

theorem v_sq_comm_t : V.D.v ^ 2 * t = t * V.D.v ^ 2 := by
  have h1 := V.v_conj_t
  have h2 : V.D.v * t = t * V.ki * V.D.v := by rw [← h1]; group
  have h3 : V.D.v * V.ki = V.ki * V.D.v := V.v_comm_E0 V.ki_mem_E0
  calc V.D.v ^ 2 * t = V.D.v * (V.D.v * t) := by rw [pow_two, mul_assoc]
    _ = V.D.v * (t * V.ki * V.D.v) := by rw [h2]
    _ = (V.D.v * t) * (V.ki * V.D.v) := by group
    _ = (t * V.ki * V.D.v) * (V.ki * V.D.v) := by rw [h2]
    _ = t * V.ki * (V.D.v * V.ki) * V.D.v := by group
    _ = t * V.ki * (V.ki * V.D.v) * V.D.v := by rw [h3]
    _ = t * (V.ki * V.ki) * (V.D.v * V.D.v) := by group
    _ = t * V.D.v ^ 2 := by rw [V.ki_sq, pow_two, mul_one]

theorem v_sq_comm_yi : V.D.v ^ 2 * V.yi = V.yi * V.D.v ^ 2 := by
  have h := V.v_comm_E0 V.yi_mem_E0
  rw [pow_two, mul_assoc, h, ← mul_assoc, h, mul_assoc]

theorem v_sq_mem_E : V.D.v ^ 2 ∈ S.E V.yi :=
  mem_E_of_mem_T₁ S V.h4 V.hyi (pow_mem V.v_mem_T₁ 2) V.v_sq_comm_t V.v_sq_comm_yi

theorem v_sq_comm_u : V.D.v ^ 2 * V.D.u = V.D.u * V.D.v ^ 2 := by
  have hc : V.D.u * V.D.v = V.D.v * V.D.u :=
    V.D.u_comm_C V.D.v (V.D.C_eq ▸ subset_closure (by simp))
  rw [pow_two, mul_assoc, ← hc, ← mul_assoc, ← hc, mul_assoc]

theorem v_sq_mem_zk : V.D.v ^ 2 ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  have h0 : V.D.v ^ 2 ∈ S.E0 V.yi V.ki :=
    V.mem_E0_of_comm_v V.v_sq_mem_E (by rw [pow_two]; group)
  have h0' : V.D.v ^ 2 ∈ S.E0 V.F.yF V.F.kF := h0
  rw [V.F.E0_eq'] at h0'
  rcases Sec7.mem_or_of_mem_sup V.F.elemAbelianTwo_zk V.F.yF_sq
    (fun _ hb => V.F.yF_comm_zk hb) h0' with h | h
  · exact h
  · exfalso
    set c := V.D.v ^ 2 * V.yi with hc
    have hv2 : V.D.v ^ 2 = c * V.yi := by
      rw [hc, mul_assoc, V.yi_sq, mul_one]
    have hcB : c ∈ S.B := V.zk_le_B h
    have h1 := V.v_sq_comm_u
    rw [hv2] at h1
    have h2 : V.D.u * (c * V.yi) * V.D.u⁻¹ = c * V.yi := by rw [← h1, mul_inv_cancel_right]
    rw [show V.D.u * (c * V.yi) * V.D.u⁻¹ = (V.D.u * c * V.D.u⁻¹) * (V.D.u * V.yi * V.D.u⁻¹) by
      group, V.u_conj_B hcB, V.u_conj_yi] at h2
    exact z_ne_one S (mul_eq_right.mp (mul_left_cancel h2))

theorem D₁₁_mem_normalizer {δ : X} (hδ : δ ∈ V.D.D₁₁) :
    δ ∈ normalizer (S.E V.yi : Set X) := (V.D.D₁₁_le hδ).1.1

theorem fix_yi_of_fix_z (hz : ∀ δ ∈ V.D.D₁₁, δ * S.z * δ⁻¹ = S.z) :
    ∀ δ ∈ V.D.D₁₁, δ * V.yi * δ⁻¹ = V.yi := by
  intro δ hδ
  have hN := V.D₁₁_mem_normalizer hδ
  have hk : δ * V.ki * δ⁻¹ = V.ki := V.D.k_fixed δ hN
  have hzδ := hz δ hδ
  have hmem := V.conj_mem_E0 hN V.yi_mem_E0
  have hmem' : δ * V.yi * δ⁻¹ ∈ S.E0 V.F.yF V.F.kF := hmem
  rw [V.F.E0_eq'] at hmem'
  rcases Sec7.mem_or_of_mem_sup V.F.elemAbelianTwo_zk V.F.yF_sq
    (fun _ hb => V.F.yF_comm_zk hb) hmem' with h | h
  · exfalso
    apply V.F.yF_not_mem_zk
    have hfix := V.conj_zk_of_fix hzδ hk h
    have : V.yi = δ * V.yi * δ⁻¹ := by
      calc V.yi = δ⁻¹ * (δ * V.yi * δ⁻¹) * δ := by group
        _ = δ⁻¹ * (δ * (δ * V.yi * δ⁻¹) * δ⁻¹) * δ := by rw [hfix]
        _ = δ * V.yi * δ⁻¹ := by group
    rw [show V.F.yF = V.yi from rfl, this]
    exact h
  · change δ * V.yi * δ⁻¹ * V.yi ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) at h
    set c := δ * V.yi * δ⁻¹ * V.yi with hc
    have hcfix := V.conj_zk_of_fix hzδ hk h
    have hdy : δ * V.yi * δ⁻¹ = c * V.yi := by
      rw [hc, mul_assoc _ V.yi V.yi, V.yi_sq, mul_one]
    clear_value c
    have hpow : ∀ n : ℕ, δ ^ n * V.yi * (δ ^ n)⁻¹ = c ^ n * V.yi := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hcn : δ * c ^ n * δ⁻¹ = c ^ n := by
          rw [show δ * c ^ n * δ⁻¹ = (δ * c * δ⁻¹) ^ n by rw [conj_pow], hcfix]
        calc δ ^ (n + 1) * V.yi * (δ ^ (n + 1))⁻¹ = δ * (δ ^ n * V.yi * (δ ^ n)⁻¹) * δ⁻¹ := by
              rw [pow_succ']; group
          _ = (δ * c ^ n * δ⁻¹) * (δ * V.yi * δ⁻¹) := by rw [ih]; group
          _ = c ^ (n + 1) * V.yi := by rw [hcn, hdy, pow_succ, mul_assoc]
    obtain ⟨m, hm⟩ := V.D.isPGroup_D₁₁ ⟨δ, hδ⟩
    have hm' : δ ^ 3 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hc2 : c ^ 2 = 1 := sq_of_mem_B S (V.zk_le_B h)
    have hodd : Odd (3 ^ m) := Odd.pow (by decide)
    obtain ⟨j, hj⟩ := hodd
    have hc1 : c ^ 3 ^ m = c := by
      rw [hj, pow_succ, pow_mul, hc2, one_pow, one_mul]
    have h1 := hpow (3 ^ m)
    rw [hm', hc1, one_mul, inv_one, mul_one] at h1
    have hc0 : c = 1 := mul_eq_right.mp h1.symm
    rw [hdy, hc0, one_mul]

theorem v_mem_C : V.D.v ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X) :=
  V.D.C_eq ▸ subset_closure (by simp)

theorem v_conj_zk {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    V.D.v * c * V.D.v⁻¹ = c := V.v_conj_E0 (V.zk_le_E0 hc)

theorem v_mem_normalizer_B : V.D.v ∈ normalizer (S.B : Set X) := by
  have hv2 : V.D.v ^ 2 ∈ S.B := V.zk_le_B V.v_sq_mem_zk
  have hfwd : ∀ b ∈ S.B, V.D.v * b * V.D.v⁻¹ ∈ S.B := by
    intro b hb
    rcases V.mem_B_cases hb with h | h
    · rw [V.v_conj_zk h]; exact hb
    · have hb' : b = b * t * t := by rw [mul_assoc, tt (A := A), mul_one]
      rw [hb', show V.D.v * (b * t * t) * V.D.v⁻¹ =
        (V.D.v * (b * t) * V.D.v⁻¹) * (V.D.v * t * V.D.v⁻¹) by group, V.v_conj_zk h,
        V.v_conj_t]
      exact mul_mem (V.zk_le_B h) (mul_mem Frame.t_mem_B V.ki_mem_B)
  rw [mem_normalizer_iff]
  intro b
  refine ⟨hfwd b, fun h => ?_⟩
  have e : b = (V.D.v ^ 2)⁻¹ * (V.D.v * (V.D.v * b * V.D.v⁻¹) * V.D.v⁻¹) * V.D.v ^ 2 := by
    group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hv2) (hfwd _ h)) hv2

theorem yi_mem_Q₁ : V.yi ∈ V.D.Q₁ := V.D.Q0_le (mem_sup_left (mem_sup_left V.yi_mem_E0))

theorem not_fix_z : ¬ ∀ δ ∈ V.D.D₁₁, δ * S.z * δ⁻¹ = S.z := by
  intro hz
  have hy := V.fix_yi_of_fix_z hz
  have hyC : V.yi ∈ centralizer (V.D.D₁₁ : Set X) := by
    rw [mem_centralizer_iff]
    intro δ hδ
    have := hy δ hδ
    calc δ * V.yi = δ * V.yi * δ⁻¹ * δ := by group
      _ = V.yi * δ := by rw [this]
  have hmem : V.yi ∈ closure ({t, V.ki, V.D.v} : Set X) := V.D.C_eq ▸ ⟨V.yi_mem_Q₁, hyC⟩
  have hle : closure ({t, V.ki, V.D.v} : Set X) ≤ S.B ⊔ zpowers V.D.v := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left Frame.t_mem_B
    · exact mem_sup_left V.ki_mem_B
    · exact mem_sup_right (mem_zpowers _)
  rcases Sec7.mem_or_of_mem_sup_zpowers V.v_mem_normalizer_B (V.zk_le_B V.v_sq_mem_zk)
    (hle hmem) with h | h
  · exact V.yi_not_mem_B h
  · have hvT : V.D.v ∈ A.T := by
      have := mul_mem (inv_mem (B_le_T S h)) V.yi_mem_T
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
    have h1 := V.v_conj_t
    rw [A.commute_t hvT, mul_inv_cancel_right] at h1
    exact V.ki_ne_one (mul_eq_left.mp h1.symm)

end ISide

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
