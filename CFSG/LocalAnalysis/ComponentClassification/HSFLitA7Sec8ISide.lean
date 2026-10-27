module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Rel

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

structure ISide (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  yi : X
  ki : X
  ui : X
  hyi : IsRefl F yi
  hki : IsK (S := S) ki
  hui : ui = F.xF * yi
  D : S.Sec6 T₁ yi ki ui
  hq : D.q0 = .elem ∨ D.q0 = .homocyclic
  hu : D.u = ui

namespace ISide

variable (V : ISide S F T₁)

theorem hact : V.D.act = .one := act_eq_one_of_comm V.hki V.D (comm_of_q0 V.D V.hq)

theorem t_comm_T {g : X} (hg : g ∈ S.data.T) : S.t * g = g * S.t := (S.data.commute_t hg).symm

theorem t_conj_T {g : X} (hg : g ∈ S.data.T) : S.t * g * S.t⁻¹ = g := by
  rw [t_comm_T hg, mul_inv_cancel_right]

theorem act : (∀ e ∈ S.E0 V.yi V.ki, V.D.v * e * V.D.v⁻¹ = e ∧ V.D.w₁ * e * V.D.w₁⁻¹ = e ∧
      V.D.w₂ * e * V.D.w₂⁻¹ = e) ∧ V.D.v * S.t * V.D.v⁻¹ = S.t * V.ki ∧
    V.D.w₁ * S.t * V.D.w₁⁻¹ = S.t * S.z ∧ V.D.w₂ * S.t * V.D.w₂⁻¹ = S.t * V.yi := by
  have h := V.D.act_holds
  rw [V.hact] at h
  exact h

theorem ki_sq : V.ki * V.ki = 1 := by rw [← pow_two, V.hki.sq]

theorem yi_sq : V.yi * V.yi = 1 := by rw [← pow_two, V.hyi.sq]

theorem ui_mem_T : V.ui ∈ S.data.T := by
  rw [V.hui]; exact mul_mem (xF_mem_T F) V.hyi.mem_T

theorem u_mem_T : V.D.u ∈ S.data.T := by rw [V.hu]; exact V.ui_mem_T

theorem u_sq : V.D.u * V.D.u = 1 := by
  rw [V.hu, V.hui, ← pow_two]; exact refl_xmul_sq V.hyi

theorem u_inv : V.D.u⁻¹ = V.D.u := by rw [inv_eq_iff_mul_eq_one, V.u_sq]

theorem u_conj_yi : V.D.u * V.yi * V.D.u⁻¹ = S.z * V.yi := by
  rw [V.hu, V.hui, show F.xF * V.yi * V.yi * (F.xF * V.yi)⁻¹ = F.xF * (V.yi * V.yi * V.yi⁻¹) *
    F.xF⁻¹ by group, mul_inv_cancel_right, refl_x_conj V.hyi]

theorem u_conj_B {b : X} (hb : b ∈ S.B) : V.D.u * b * V.D.u⁻¹ = b := by
  rw [← S.central_of_mem_B hb V.u_mem_T, mul_inv_cancel_right]

theorem u_conj_t : V.D.u * S.t * V.D.u⁻¹ = S.t := V.u_conj_B t_mem_B

theorem u_conj_z : V.D.u * S.z * V.D.u⁻¹ = S.z := V.u_conj_B z_mem_B

theorem u_conj_ki : V.D.u * V.ki * V.D.u⁻¹ = V.ki := V.u_conj_B V.hki.mem

theorem u_mem_S₁ : V.D.u ∈ V.D.S₁ := u_mem_S₁_of V.D

theorem w₂_mem_S₁ : V.D.w₂ ∈ V.D.S₁ := w₂_mem_S₁_of V.D

theorem v_mem_S₁ : V.D.v ∈ V.D.S₁ := V.D.T₁_le (v_mem_T₁ V.D)

theorem eq_of_mem_zk {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    c = 1 ∨ c = S.z ∨ c = V.ki ∨ c = S.z * V.ki := by
  have hz : ElemAbelianTwo (zpowers S.z) :=
    ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr z_mem_B ha) (zpowers_le.mpr z_mem_B hb),
      fun a ha => S.sq_of_mem_B (zpowers_le.mpr z_mem_B ha)⟩
  rcases mem_or_of_mem_sup hz V.hki.sq
    (fun a ha => commute_of_mem_B V.hki.mem (zpowers_le.mpr z_mem_B ha)) hc with h | h
  · rcases eq_one_or_eq_of_mem_zpowers z_sq h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases eq_one_or_eq_of_mem_zpowers z_sq h with h | h
    · right; right; left
      calc c = c * V.ki * V.ki := by rw [mul_assoc, V.ki_sq, mul_one]
        _ = V.ki := by rw [h, one_mul]
    · right; right; right
      calc c = c * V.ki * V.ki := by rw [mul_assoc, V.ki_sq, mul_one]
        _ = S.z * V.ki := by rw [h]

theorem zk_le_E0 : (zpowers S.z ⊔ zpowers V.ki : Subgroup X) ≤ S.E0 V.yi V.ki := by
  rw [E0_eq]; exact le_sup_left

theorem conj_zk_of_fix {g : X} (hz : g * S.z * g⁻¹ = S.z) (hk : g * V.ki * g⁻¹ = V.ki) {c : X}
    (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) : g * c * g⁻¹ = c := by
  rcases V.eq_of_mem_zk hc with rfl | rfl | rfl | rfl
  · group
  · exact hz
  · exact hk
  · rw [show g * (S.z * V.ki) * g⁻¹ = (g * S.z * g⁻¹) * (g * V.ki * g⁻¹) by group, hz, hk]

theorem t_not_mem_zk : S.t ∉ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := fun h =>
  V.hyi.t_not_mem_E0 V.hki (V.zk_le_E0 h)

theorem B_eq : S.B = (zpowers S.z ⊔ zpowers V.ki) ⊔ zpowers S.t := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (sup_le (zk_le_B V.hki) (zpowers_le.mpr t_mem_B)) ?_
  rw [S.card_B, card_sup_of_not_mem (elemAbelianTwo_zk V.hki) S.t_sq V.t_not_mem_zk
    (fun a ha => (commute_of_mem_B (zk_le_B V.hki ha) t_mem_B).symm), card_zk V.hki]

theorem mem_B_cases {b : X} (hb : b ∈ S.B) :
    b ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) ∨
      b * S.t ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  rw [V.B_eq] at hb
  exact mem_or_of_mem_sup (elemAbelianTwo_zk V.hki) S.t_sq
    (fun a ha => (commute_of_mem_B (zk_le_B V.hki ha) t_mem_B).symm) hb

theorem mem_E0_of_comm_v {e : X} (he : e ∈ S.E V.yi) (hv : V.D.v * e * V.D.v⁻¹ = e) :
    e ∈ S.E0 V.yi V.ki := by
  rcases V.hyi.mem_E0_or V.hki he with h | h
  · exact h
  · exfalso
    have h1 := v_conj_E0 V.D h
    have h2 : V.D.v * (e * S.t) * V.D.v⁻¹ = e * (S.t * V.ki) := by
      rw [show V.D.v * (e * S.t) * V.D.v⁻¹ = (V.D.v * e * V.D.v⁻¹) * (V.D.v * S.t * V.D.v⁻¹)
        by group, hv, v_conj_t V.D]
    rw [h1, ← mul_assoc] at h2
    exact V.hki.ne_one (mul_eq_left.mp h2.symm)

theorem conj_mem_E0 {n : X} (hn : n ∈ normalizer (S.E V.yi : Set X)) {e : X}
    (he : e ∈ S.E0 V.yi V.ki) : n * e * n⁻¹ ∈ S.E0 V.yi V.ki := by
  have heE : e ∈ S.E V.yi := E0_le_E V.hki V.yi he
  refine V.mem_E0_of_comm_v (conj_mem_of_mem_normalizer hn heE) ?_
  have hc := V.D.v_central n⁻¹ (inv_mem hn)
  rw [inv_inv] at hc
  set c := n⁻¹ * V.D.v * n * V.D.v⁻¹ with hcdef
  have hce : c * e = e * c := (mem_centralizer_iff.mp hc e heE).symm
  have hv : n⁻¹ * V.D.v * n = c * V.D.v := by rw [hcdef]; group
  calc V.D.v * (n * e * n⁻¹) * V.D.v⁻¹ = n * (n⁻¹ * V.D.v * n) * e * (n⁻¹ * V.D.v * n)⁻¹ * n⁻¹ := by
        group
    _ = n * (c * (V.D.v * e * V.D.v⁻¹) * c⁻¹) * n⁻¹ := by rw [hv]; group
    _ = n * e * n⁻¹ := by rw [v_conj_E0 V.D he, hce]; group

theorem v_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.v * e = e * V.D.v := by
  have h := v_conj_E0 V.D he
  calc V.D.v * e = V.D.v * e * V.D.v⁻¹ * V.D.v := by group
    _ = e * V.D.v := by rw [h]

theorem v_sq_comm_t : V.D.v ^ 2 * S.t = S.t * V.D.v ^ 2 := by
  have h1 := v_conj_t V.D
  have h2 : V.D.v * S.t = S.t * V.ki * V.D.v := by rw [← h1]; group
  have h3 : V.D.v * V.ki = V.ki * V.D.v := V.v_comm_E0 (ki_mem_E0 _ _)
  calc V.D.v ^ 2 * S.t = V.D.v * (V.D.v * S.t) := by rw [pow_two, mul_assoc]
    _ = V.D.v * (S.t * V.ki * V.D.v) := by rw [h2]
    _ = (V.D.v * S.t) * (V.ki * V.D.v) := by group
    _ = (S.t * V.ki * V.D.v) * (V.ki * V.D.v) := by rw [h2]
    _ = S.t * V.ki * (V.D.v * V.ki) * V.D.v := by group
    _ = S.t * V.ki * (V.ki * V.D.v) * V.D.v := by rw [h3]
    _ = S.t * (V.ki * V.ki) * (V.D.v * V.D.v) := by group
    _ = S.t * V.D.v ^ 2 := by rw [V.ki_sq, pow_two, mul_one]

theorem v_sq_centralizes : ∀ e ∈ S.E V.yi, V.D.v ^ 2 * e * (V.D.v ^ 2)⁻¹ = e := by
  have hle : S.E V.yi ≤ centralizer ({V.D.v ^ 2} : Set X) := by
    rw [V.hyi.E_eq_E0_sup V.hki]
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      have h := V.v_comm_E0 he
      symm
      calc V.D.v ^ 2 * e = V.D.v * (V.D.v * e) := by rw [pow_two, mul_assoc]
        _ = V.D.v * (e * V.D.v) := by rw [h]
        _ = (V.D.v * e) * V.D.v := by group
        _ = (e * V.D.v) * V.D.v := by rw [h]
        _ = e * V.D.v ^ 2 := by rw [pow_two]; group
    · rw [mem_centralizer_singleton_iff]
      exact V.v_sq_comm_t.symm
  intro e he
  have := mem_centralizer_singleton_iff.mp (hle he)
  rw [← this, mul_inv_cancel_right]

theorem v_sq_mem_E : V.D.v ^ 2 ∈ S.E V.yi :=
  mem_E_of_centralizes V.hyi V.D.isPGroup_S₁ (pow_mem V.v_mem_S₁ 2) V.v_sq_centralizes

theorem v_sq_comm_u : V.D.v ^ 2 * V.D.u = V.D.u * V.D.v ^ 2 := by
  rw [pow_two, mul_assoc, ← u_comm_v V.D, ← mul_assoc, ← u_comm_v V.D, mul_assoc]

theorem v_sq_mem_zk : V.D.v ^ 2 ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  have h0 : V.D.v ^ 2 ∈ S.E0 V.yi V.ki :=
    V.mem_E0_of_comm_v V.v_sq_mem_E (by rw [pow_two]; group)
  rw [E0_eq] at h0
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk V.hki) V.hyi.sq
    (fun _ hb => V.hyi.comm_B (zk_le_B V.hki hb)) h0 with h | h
  · exact h
  · exfalso
    set c := V.D.v ^ 2 * V.yi with hc
    have hv2 : V.D.v ^ 2 = c * V.yi := by
      rw [hc, mul_assoc, ← pow_two, V.hyi.sq, mul_one]
    have hcB : c ∈ S.B := zk_le_B V.hki h
    have h1 := V.v_sq_comm_u
    rw [hv2] at h1
    have h2 : V.D.u * (c * V.yi) * V.D.u⁻¹ = c * V.yi := by rw [← h1, mul_inv_cancel_right]
    rw [show V.D.u * (c * V.yi) * V.D.u⁻¹ = (V.D.u * c * V.D.u⁻¹) * (V.D.u * V.yi * V.D.u⁻¹) by
      group, V.u_conj_B hcB, V.u_conj_yi] at h2
    exact S.z_ne_one (mul_eq_right.mp (mul_left_cancel h2))

theorem D₁₁_mem_normalizer {δ : X} (hδ : δ ∈ V.D.D₁₁) :
    δ ∈ normalizer (S.E V.yi : Set X) := (V.D.D₁₁_le hδ).1.1

theorem fix_yi_of_fix_z (hz : ∀ δ ∈ V.D.D₁₁, δ * S.z * δ⁻¹ = S.z) :
    ∀ δ ∈ V.D.D₁₁, δ * V.yi * δ⁻¹ = V.yi := by
  intro δ hδ
  have hN := V.D₁₁_mem_normalizer hδ
  have hk : δ * V.ki * δ⁻¹ = V.ki := V.D.k_fixed δ hN
  have hzδ := hz δ hδ
  have hmem := V.conj_mem_E0 hN (yi_mem_E0 V.yi V.ki)
  rw [E0_eq] at hmem
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk V.hki) V.hyi.sq
    (fun _ hb => V.hyi.comm_B (zk_le_B V.hki hb)) hmem with h | h
  · exfalso
    apply V.hyi.not_mem_B
    have hfix := V.conj_zk_of_fix hzδ hk h
    have : V.yi = δ * V.yi * δ⁻¹ := by
      calc V.yi = δ⁻¹ * (δ * V.yi * δ⁻¹) * δ := by group
        _ = δ⁻¹ * (δ * (δ * V.yi * δ⁻¹) * δ⁻¹) * δ := by rw [hfix]
        _ = δ * V.yi * δ⁻¹ := by group
    rw [this]
    exact zk_le_B V.hki h
  · set c := δ * V.yi * δ⁻¹ * V.yi with hc
    have hcfix := V.conj_zk_of_fix hzδ hk h
    have hdy : δ * V.yi * δ⁻¹ = c * V.yi := by
      rw [hc, mul_assoc _ V.yi V.yi, ← pow_two, V.hyi.sq, mul_one]
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
    have hc2 : c ^ 2 = 1 := S.sq_of_mem_B (zk_le_B V.hki h)
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
    V.D.v * c * V.D.v⁻¹ = c := v_conj_E0 V.D (V.zk_le_E0 hc)

theorem v_mem_normalizer_B : V.D.v ∈ normalizer (S.B : Set X) := by
  have hv2 : V.D.v ^ 2 ∈ S.B := zk_le_B V.hki V.v_sq_mem_zk
  have hfwd : ∀ b ∈ S.B, V.D.v * b * V.D.v⁻¹ ∈ S.B := by
    intro b hb
    rcases V.mem_B_cases hb with h | h
    · rw [V.v_conj_zk h]; exact hb
    · have hb' : b = b * S.t * S.t := by rw [mul_assoc, ← pow_two, S.t_sq, mul_one]
      rw [hb', show V.D.v * (b * S.t * S.t) * V.D.v⁻¹ =
        (V.D.v * (b * S.t) * V.D.v⁻¹) * (V.D.v * S.t * V.D.v⁻¹) by group, V.v_conj_zk h,
        v_conj_t V.D]
      exact mul_mem (zk_le_B V.hki h) (mul_mem t_mem_B V.hki.mem)
  rw [mem_normalizer_iff]
  intro b
  refine ⟨hfwd b, fun h => ?_⟩
  have e : b = (V.D.v ^ 2)⁻¹ * (V.D.v * (V.D.v * b * V.D.v⁻¹) * V.D.v⁻¹) * V.D.v ^ 2 := by
    group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hv2) (hfwd _ h)) hv2

theorem yi_mem_Q₁ : V.yi ∈ V.D.Q₁ :=
  V.D.Q0_le (mem_sup_left (mem_sup_left (yi_mem_E0 V.yi V.ki)))

theorem not_fix_z : ¬ ∀ δ ∈ V.D.D₁₁, δ * S.z * δ⁻¹ = S.z := by
  intro hz
  have hy := V.fix_yi_of_fix_z hz
  have hyC : V.yi ∈ centralizer (V.D.D₁₁ : Set X) := by
    rw [mem_centralizer_iff]
    intro δ hδ
    have := hy δ hδ
    calc δ * V.yi = δ * V.yi * δ⁻¹ * δ := by group
      _ = V.yi * δ := by rw [this]
  have hmem : V.yi ∈ closure ({S.t, V.ki, V.D.v} : Set X) := V.D.C_eq ▸ ⟨V.yi_mem_Q₁, hyC⟩
  have hle : closure ({S.t, V.ki, V.D.v} : Set X) ≤ S.B ⊔ zpowers V.D.v := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left t_mem_B
    · exact mem_sup_left V.hki.mem
    · exact mem_sup_right (mem_zpowers _)
  rcases mem_or_of_mem_sup_zpowers V.v_mem_normalizer_B (zk_le_B V.hki V.v_sq_mem_zk)
    (hle hmem) with h | h
  · exact V.hyi.not_mem_B h
  · have hvT : V.D.v ∈ S.data.T := by
      have := mul_mem (inv_mem (S.B_le_T h)) V.hyi.mem_T
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
    have h1 := v_conj_t V.D
    rw [S.data.commute_t hvT, mul_inv_cancel_right] at h1
    exact V.hki.ne_one (mul_eq_left.mp h1.symm)

theorem v_sq_eq : V.D.v ^ 2 = 1 ∨ V.D.v ^ 2 = V.ki := by
  have hvC := (V.v_mem_C).2
  have hv2C : V.D.v ^ 2 ∈ centralizer (V.D.D₁₁ : Set X) := pow_mem hvC 2
  have hfix : ∀ g ∈ centralizer (V.D.D₁₁ : Set X), ∀ δ ∈ V.D.D₁₁, δ * g * δ⁻¹ = g := by
    intro g hg δ hδ
    rw [(mem_centralizer_iff.mp hg) δ hδ, mul_inv_cancel_right]
  rcases V.eq_of_mem_zk V.v_sq_mem_zk with h | h | h | h
  · exact Or.inl h
  · exfalso
    exact V.not_fix_z (fun δ hδ => h ▸ hfix _ hv2C δ hδ)
  · exact Or.inr h
  · exfalso
    apply V.not_fix_z
    intro δ hδ
    have h1 := hfix _ hv2C δ hδ
    rw [h] at h1
    have h2 : δ * V.ki * δ⁻¹ = V.ki := V.D.k_fixed δ (V.D₁₁_mem_normalizer hδ)
    calc δ * S.z * δ⁻¹ = (δ * (S.z * V.ki) * δ⁻¹) * (δ * V.ki * δ⁻¹)⁻¹ := by group
      _ = S.z := by rw [h1, h2, mul_inv_cancel_right]

open Classical in
noncomputable def vN : X := if V.D.v ^ 2 = 1 then V.D.v else V.D.v * S.t

theorem vN_eq : V.vN = V.D.v ∨ V.vN = V.D.v * S.t := by
  unfold vN
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem vN_sq : V.vN ^ 2 = 1 := by
  unfold vN
  split_ifs with h
  · exact h
  · have hk : V.D.v ^ 2 = V.ki := V.v_sq_eq.resolve_left h
    have ht := v_conj_t V.D
    calc (V.D.v * S.t) ^ 2 = (V.D.v * S.t * V.D.v⁻¹) * V.D.v ^ 2 * S.t := by
          rw [pow_two, pow_two]; group
      _ = 1 := by
        rw [ht, hk, mul_assoc S.t, V.ki_sq, mul_one, ← pow_two, S.t_sq]

theorem vN_mul_vN : V.vN * V.vN = 1 := by rw [← pow_two, V.vN_sq]

theorem vN_conj_T_of_conj {g : X} (hg : g ∈ S.data.T) :
    V.vN * g * V.vN⁻¹ = V.D.v * g * V.D.v⁻¹ := by
  unfold vN
  split_ifs
  · rfl
  · rw [show V.D.v * S.t * g * (V.D.v * S.t)⁻¹ = V.D.v * (S.t * g * S.t⁻¹) * V.D.v⁻¹ by group,
      t_conj_T hg]

theorem vN_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.vN * e * V.vN⁻¹ = e := by
  rw [V.vN_conj_T_of_conj (V.hyi.E_le_T (E0_le_E V.hki V.yi he)), v_conj_E0 V.D he]

theorem vN_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.vN * e = e * V.vN := by
  have h := V.vN_conj_E0 he
  calc V.vN * e = V.vN * e * V.vN⁻¹ * V.vN := by group
    _ = e * V.vN := by rw [h]

theorem vN_conj_t : V.vN * S.t * V.vN⁻¹ = S.t * V.ki := by
  rw [V.vN_conj_T_of_conj S.data.t_mem_T, v_conj_t V.D]

theorem vN_conj_z : V.vN * S.z * V.vN⁻¹ = S.z := V.vN_conj_E0 (z_mem_E0 _ _)

theorem vN_conj_yi : V.vN * V.yi * V.vN⁻¹ = V.yi := V.vN_conj_E0 (yi_mem_E0 _ _)

theorem vN_conj_ki : V.vN * V.ki * V.vN⁻¹ = V.ki := V.vN_conj_E0 (ki_mem_E0 _ _)

theorem u_comm_vN : V.D.u * V.vN = V.vN * V.D.u := by
  unfold vN
  split_ifs
  · exact u_comm_v V.D
  · rw [← mul_assoc, u_comm_v V.D, mul_assoc, ← t_comm_T V.u_mem_T, mul_assoc]

theorem vN_mem_closure : V.vN ∈ closure ({S.t, V.ki, V.D.v} : Set X) := by
  unfold vN
  split_ifs
  · exact subset_closure (by simp)
  · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem vN_mem_C : V.vN ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X) :=
  V.D.C_eq ▸ V.vN_mem_closure

include V in
theorem T_le_T₁ : S.data.T ≤ T₁ := by
  rw [V.D.T₁_eq]; exact le_sup_left.trans le_sup_left

include V in
theorem t_mem_T₁ : S.t ∈ T₁ := V.T_le_T₁ S.data.t_mem_T

theorem vN_mem_T₁ : V.vN ∈ T₁ := by
  unfold vN
  split_ifs
  · exact v_mem_T₁ V.D
  · exact mul_mem (v_mem_T₁ V.D) V.t_mem_T₁

theorem vN_mem_S₁ : V.vN ∈ V.D.S₁ := V.D.T₁_le V.vN_mem_T₁

theorem mem_C {c : X} (hc : c ∈ closure ({S.t, V.ki, V.D.v} : Set X)) :
    c ∈ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) ∨
      c * V.vN⁻¹ ∈ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) := by
  have hN : V.vN ∈ normalizer ((zpowers V.ki ⊔ zpowers S.t : Subgroup X) : Set X) :=
    mem_normalizer_of_conj_gens' (by rw [V.vN_conj_ki]; exact mem_sup_left (mem_zpowers _))
      (by rw [V.vN_conj_t]
          exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _)))
  have hv2 : V.vN ^ 2 ∈ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) := by
    rw [V.vN_sq]; exact one_mem _
  have hle : closure ({S.t, V.ki, V.D.v} : Set X) ≤
      (zpowers V.ki ⊔ zpowers S.t : Subgroup X) ⊔ zpowers V.vN := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_left (mem_sup_left (mem_zpowers _))
    · rcases V.vN_eq with h | h
      · rw [← h]; exact mem_sup_right (mem_zpowers _)
      · have : V.D.v = V.vN * S.t⁻¹ := by rw [h]; group
        rw [this]
        exact mul_mem (mem_sup_right (mem_zpowers _))
          (mem_sup_left (mem_sup_right (inv_mem (mem_zpowers _))))
  exact mem_or_of_mem_sup_zpowers hN hv2 (hle hc)

theorem w₁_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.w₁ * e * V.D.w₁⁻¹ = e :=
  (V.act.1 e he).2.1

theorem w₂_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.w₂ * e * V.D.w₂⁻¹ = e :=
  (V.act.1 e he).2.2

theorem w₁_conj_t : V.D.w₁ * S.t * V.D.w₁⁻¹ = S.t * S.z := V.act.2.2.1

theorem w₂_conj_t : V.D.w₂ * S.t * V.D.w₂⁻¹ = S.t * V.yi := V.act.2.2.2

theorem Q0_comm {a b : X} (ha : a ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂)
    (hb : b ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂) : a * b = b * a :=
  comm_of_q0 V.D V.hq a ha b hb

theorem E0_le_Q0 : S.E0 V.yi V.ki ≤ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ := le_sup_left.trans le_sup_left

theorem w₁_sq_of_elem (h : V.D.q0 = .elem) : V.D.w₁ ^ 2 = 1 := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.2.1 _ (w₁_mem_Q0 _ _ _ _)

theorem w₂_sq_of_elem (h : V.D.q0 = .elem) : V.D.w₂ ^ 2 = 1 := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.2.1 _ (w₂_mem_Q0 _ _ _ _)

theorem w₁_sq_of_homoc (h : V.D.q0 = .homocyclic) : V.D.w₁ ^ 2 = S.z := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.1

theorem w₂_sq_of_homoc (h : V.D.q0 = .homocyclic) : V.D.w₂ ^ 2 = V.yi := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.2.1

theorem w₁_sq_mem : V.D.w₁ ^ 2 ∈ S.E0 V.yi V.ki := by
  rcases V.hq with h | h
  · rw [V.w₁_sq_of_elem h]; exact one_mem _
  · rw [V.w₁_sq_of_homoc h]; exact z_mem_E0 _ _

theorem w₁_mem_normalizer_E0 : V.D.w₁ ∈ normalizer (S.E0 V.yi V.ki : Set X) := by
  rw [mem_normalizer_iff]
  intro e
  refine ⟨fun he => by rw [V.w₁_conj_E0 he]; exact he, fun he => ?_⟩
  have h1 := V.w₁_conj_E0 he
  have : e = V.D.w₁ * e * V.D.w₁⁻¹ := by
    calc e = V.D.w₁⁻¹ * (V.D.w₁ * e * V.D.w₁⁻¹) * V.D.w₁ := by group
      _ = V.D.w₁⁻¹ * (V.D.w₁ * (V.D.w₁ * e * V.D.w₁⁻¹) * V.D.w₁⁻¹) * V.D.w₁ := by rw [h1]
      _ = V.D.w₁ * e * V.D.w₁⁻¹ := by group
  rw [this]; exact he

@[expose] noncomputable def w₁N : X := V.D.u⁻¹ * V.D.w₂ * V.D.u * V.D.w₂⁻¹

theorem w₁N_def : V.w₁N = V.D.u⁻¹ * V.D.w₂ * V.D.u * V.D.w₂⁻¹ := rfl

theorem w₂_conj_u : V.D.w₂ * V.D.u * V.D.w₂⁻¹ = V.D.u * V.w₁N := by rw [w₁N_def]; group

theorem w₂_inv_conj_t : V.D.w₂⁻¹ * S.t * V.D.w₂ = S.t * V.yi := by
  have h1 := V.w₂_conj_t
  have h2 := V.w₂_conj_E0 (yi_mem_E0 V.yi V.ki)
  calc V.D.w₂⁻¹ * S.t * V.D.w₂ = V.D.w₂⁻¹ * (S.t * V.yi * V.yi) * V.D.w₂ := by
        rw [mul_assoc S.t, V.yi_sq, mul_one]
    _ = V.D.w₂⁻¹ * ((V.D.w₂ * S.t * V.D.w₂⁻¹) * (V.D.w₂ * V.yi * V.D.w₂⁻¹)) * V.D.w₂ := by
        rw [h1, h2]
    _ = S.t * V.yi := by group

theorem w₁N_eq : ∃ e ∈ S.E0 V.yi V.ki, V.w₁N = V.D.w₁ * e := by
  have hc : V.w₁N ∈ S.E0 V.yi V.ki ⊔ zpowers V.D.w₁ := by
    have := V.D.S₁_commutator_mem _ (inv_mem V.u_mem_S₁) _ V.w₂_mem_S₁
    rwa [inv_inv] at this
  rcases mem_or_of_mem_sup_zpowers V.w₁_mem_normalizer_E0 V.w₁_sq_mem hc with h | h
  · exfalso
    have h1 : (V.D.w₂ * V.D.u * V.D.w₂⁻¹) * S.t * (V.D.w₂ * V.D.u * V.D.w₂⁻¹)⁻¹ = S.t * S.z := by
      calc (V.D.w₂ * V.D.u * V.D.w₂⁻¹) * S.t * (V.D.w₂ * V.D.u * V.D.w₂⁻¹)⁻¹ =
          V.D.w₂ * (V.D.u * (V.D.w₂⁻¹ * S.t * V.D.w₂) * V.D.u⁻¹) * V.D.w₂⁻¹ := by group
        _ = V.D.w₂ * ((V.D.u * S.t * V.D.u⁻¹) * (V.D.u * V.yi * V.D.u⁻¹)) * V.D.w₂⁻¹ := by
          rw [V.w₂_inv_conj_t]; group
        _ = (V.D.w₂ * S.t * V.D.w₂⁻¹) * (V.D.w₂ * S.z * V.D.w₂⁻¹) *
            (V.D.w₂ * V.yi * V.D.w₂⁻¹) := by rw [V.u_conj_t, V.u_conj_yi]; group
        _ = S.t * V.yi * S.z * V.yi := by
          rw [V.w₂_conj_t, V.w₂_conj_E0 (z_mem_E0 _ _), V.w₂_conj_E0 (yi_mem_E0 _ _)]
        _ = S.t * S.z := by
          rw [mul_assoc S.t, V.hyi.comm_B z_mem_B, mul_assoc, mul_assoc, V.yi_sq, mul_one]
    have h2 : (V.D.u * V.w₁N) * S.t * (V.D.u * V.w₁N)⁻¹ = S.t := by
      have hct : V.w₁N * S.t * V.w₁N⁻¹ = S.t := by
        rw [← V.hyi.comm_E0_t V.hki h, mul_inv_cancel_right]
      calc (V.D.u * V.w₁N) * S.t * (V.D.u * V.w₁N)⁻¹ =
          V.D.u * (V.w₁N * S.t * V.w₁N⁻¹) * V.D.u⁻¹ := by group
        _ = S.t := by rw [hct, V.u_conj_t]
    rw [V.w₂_conj_u, h2] at h1
    exact S.z_ne_one (mul_eq_left.mp h1.symm)
  · refine ⟨V.D.w₁⁻¹ * V.w₁N, ?_, by group⟩
    have := conj_mem_of_mem_normalizer (inv_mem V.w₁_mem_normalizer_E0) h
    rwa [show V.D.w₁⁻¹ * (V.w₁N * V.D.w₁⁻¹) * V.D.w₁⁻¹⁻¹ = V.D.w₁⁻¹ * V.w₁N by group] at this

theorem E0_comm {a b : X} (ha : a ∈ S.E0 V.yi V.ki) (hb : b ∈ S.E0 V.yi V.ki) : a * b = b * a :=
  (V.hyi.elemAbelianTwo_E0 V.hki).comm a ha b hb

theorem w₁N_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.w₁N * e * V.w₁N⁻¹ = e := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw, show V.D.w₁ * c * e * (V.D.w₁ * c)⁻¹ = V.D.w₁ * (c * e * c⁻¹) * V.D.w₁⁻¹ by group,
    conj_eq_of_comm' (V.E0_comm hc he), V.w₁_conj_E0 he]

theorem w₁N_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.w₁N * e = e * V.w₁N := by
  have h := V.w₁N_conj_E0 he
  calc V.w₁N * e = V.w₁N * e * V.w₁N⁻¹ * V.w₁N := by group
    _ = e * V.w₁N := by rw [h]

theorem w₁N_conj_t : V.w₁N * S.t * V.w₁N⁻¹ = S.t * S.z := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw, show V.D.w₁ * c * S.t * (V.D.w₁ * c)⁻¹ = V.D.w₁ * (c * S.t * c⁻¹) * V.D.w₁⁻¹ by group,
    ← V.hyi.comm_E0_t V.hki hc, mul_inv_cancel_right, V.w₁_conj_t]

theorem w₁N_mem_Q0 : V.w₁N ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw]; exact mul_mem (w₁_mem_Q0 _ _ _ _) (V.E0_le_Q0 hc)

theorem w₂_comm_w₁N : V.D.w₂ * V.w₁N = V.w₁N * V.D.w₂ :=
  V.Q0_comm (w₂_mem_Q0 _ _ _ _) V.w₁N_mem_Q0

theorem w₁N_sq_eq : V.w₁N ^ 2 = V.D.w₁ ^ 2 := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  have hcw : V.D.w₁ * c = c * V.D.w₁ := V.Q0_comm (w₁_mem_Q0 _ _ _ _) (V.E0_le_Q0 hc)
  have hc2 : c * c = 1 := by
    rw [← pow_two]; exact (V.hyi.elemAbelianTwo_E0 V.hki).sq_eq_one c hc
  rw [hw, pow_two, pow_two, show V.D.w₁ * c * (V.D.w₁ * c) = V.D.w₁ * (c * V.D.w₁) * c by group,
    ← hcw, show V.D.w₁ * (V.D.w₁ * c) * c = V.D.w₁ * V.D.w₁ * (c * c) by group, hc2, mul_one]

theorem w₁N_sq_of_elem (h : V.D.q0 = .elem) : V.w₁N ^ 2 = 1 := by
  rw [V.w₁N_sq_eq, V.w₁_sq_of_elem h]

theorem w₁N_sq_of_homoc (h : V.D.q0 = .homocyclic) : V.w₁N ^ 2 = S.z := by
  rw [V.w₁N_sq_eq, V.w₁_sq_of_homoc h]

theorem u_conj_w₁N : V.D.u * V.w₁N * V.D.u⁻¹ = V.w₁N⁻¹ := by
  have h1 : (V.D.u * V.w₁N) * (V.D.u * V.w₁N) = 1 := by
    rw [← V.w₂_conj_u, show V.D.w₂ * V.D.u * V.D.w₂⁻¹ * (V.D.w₂ * V.D.u * V.D.w₂⁻¹) =
      V.D.w₂ * (V.D.u * V.D.u) * V.D.w₂⁻¹ by group, V.u_sq, mul_one, mul_inv_cancel]
  rw [V.u_inv]
  calc V.D.u * V.w₁N * V.D.u = (V.D.u * V.w₁N) * (V.D.u * V.w₁N) * V.w₁N⁻¹ := by group
    _ = V.w₁N⁻¹ := by rw [h1, one_mul]

theorem u_conj_w₁N_of_elem (h : V.D.q0 = .elem) : V.D.u * V.w₁N * V.D.u⁻¹ = V.w₁N := by
  rw [V.u_conj_w₁N, inv_eq_iff_mul_eq_one, ← pow_two, V.w₁N_sq_of_elem h]

theorem u_conj_w₁N_of_homoc (h : V.D.q0 = .homocyclic) :
    V.D.u * V.w₁N * V.D.u⁻¹ = V.w₁N * S.z := by
  rw [V.u_conj_w₁N, inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, V.w₁N_sq_of_homoc h,
    z_mul_z]

theorem w₁N_mem_T₁ : V.w₁N ∈ T₁ := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw]
  exact mul_mem (w₁_mem_T₁ V.D) (V.T_le_T₁ (V.hyi.E_le_T (E0_le_E V.hki V.yi hc)))

theorem w₁N_mem_S₁ : V.w₁N ∈ V.D.S₁ := V.D.T₁_le V.w₁N_mem_T₁

theorem w₁_eq : ∃ c ∈ S.E0 V.yi V.ki, V.D.w₁ = V.w₁N * c := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  exact ⟨c⁻¹, inv_mem hc, by rw [hw]; group⟩

theorem elemAbelianTwo_ki : ElemAbelianTwo (zpowers V.ki) :=
  ⟨fun _ ha _ hb => commute_of_mem_B (zpowers_le.mpr V.hki.mem ha) (zpowers_le.mpr V.hki.mem hb),
    fun _ ha => S.sq_of_mem_B (zpowers_le.mpr V.hki.mem ha)⟩

theorem t_not_mem_ki : S.t ∉ zpowers V.ki := fun h => V.t_not_mem_zk (mem_sup_right h)

theorem card_kt : Nat.card (zpowers V.ki ⊔ zpowers S.t : Subgroup X) = 4 := by
  rw [card_sup_of_not_mem V.elemAbelianTwo_ki S.t_sq V.t_not_mem_ki
    (fun a ha => commute_of_mem_B t_mem_B (zpowers_le.mpr V.hki.mem ha)), Nat.card_zpowers,
    orderOf_eq_prime V.hki.sq V.hki.ne_one]

theorem option : (V.D.w₂ * V.vN = V.vN * V.D.w₂ ∧ V.w₁N * V.vN = V.vN * V.w₁N) ∨
    (V.D.w₂ * V.vN * V.D.w₂⁻¹ = V.vN * V.yi ∧ V.w₁N * V.vN * V.w₁N⁻¹ = V.vN * S.z) := by
  obtain ⟨c, hc₁, hc⟩ : ∃ c ∈ V.D.C₁, c ∉ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) := by
    by_contra hne
    push Not at hne
    have hle : V.D.C₁ ⊔ zpowers S.t ≤ zpowers V.ki ⊔ zpowers S.t :=
      sup_le (fun c hc => hne c hc) le_sup_right
    rw [V.D.C₁_sup] at hle
    have := Subgroup.card_le_of_le hle
    rw [V.D.card_C, V.card_kt] at this
    norm_num at this
  have hcC : c ∈ closure ({S.t, V.ki, V.D.v} : Set X) := V.D.C_eq ▸ V.D.C₁_le hc₁
  have hcomm : ∀ q ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂, c * q = q * c :=
    fun q hq => V.D.C₁_comm c hc₁ q hq
  rcases V.mem_C hcC with h | h
  · exact absurd h hc
  have hcd : c = c * V.vN⁻¹ * V.vN := by group
  rcases mem_or_of_mem_sup V.elemAbelianTwo_ki S.t_sq
    (fun a ha => commute_of_mem_B t_mem_B (zpowers_le.mpr V.hki.mem ha)) h with h' | h'
  ·
    left
    obtain ⟨d, hdE, hcd'⟩ : ∃ d ∈ S.E0 V.yi V.ki, c = d * V.vN :=
      ⟨c * V.vN⁻¹, V.zk_le_E0 (mem_sup_right h'), by group⟩
    have key : ∀ q ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂, d * q = q * d → q * V.vN = V.vN * q := by
      intro q hq hdq
      have h1 := hcomm q hq
      rw [hcd'] at h1
      have : d * (V.vN * q) = d * (q * V.vN) := by
        calc d * (V.vN * q) = d * V.vN * q := by group
          _ = q * (d * V.vN) := h1
          _ = (q * d) * V.vN := by group
          _ = (d * q) * V.vN := by rw [hdq]
          _ = d * (q * V.vN) := by group
      exact (mul_left_cancel this).symm
    refine ⟨key _ (w₂_mem_Q0 _ _ _ _) ?_, key _ V.w₁N_mem_Q0 ?_⟩
    · have := V.w₂_conj_E0 hdE
      calc d * V.D.w₂ = V.D.w₂ * (V.D.w₂⁻¹ * d * V.D.w₂) := by group
        _ = V.D.w₂ * d := by
          congr 1
          calc V.D.w₂⁻¹ * d * V.D.w₂ = V.D.w₂⁻¹ * (V.D.w₂ * d * V.D.w₂⁻¹) * V.D.w₂ := by rw [this]
            _ = d := by group
    · exact (V.w₁N_comm_E0 hdE).symm
  ·
    right
    obtain ⟨d, hdE, hct⟩ : ∃ d ∈ S.E0 V.yi V.ki, c = d * (S.t * V.vN) := by
      refine ⟨c * V.vN⁻¹ * S.t, V.zk_le_E0 (mem_sup_right h'), ?_⟩
      calc c = c * V.vN⁻¹ * (S.t * S.t) * V.vN := by rw [t_mul_t]; group
        _ = c * V.vN⁻¹ * S.t * (S.t * V.vN) := by group
    have key : ∀ q ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂, q * d * q⁻¹ = d →
        q * (S.t * V.vN) * q⁻¹ = S.t * V.vN := by
      intro q hq hdq
      have h1 := hcomm q hq
      have h2 : q * c * q⁻¹ = c := by rw [← h1, mul_inv_cancel_right]
      rw [hct, show q * (d * (S.t * V.vN)) * q⁻¹ = (q * d * q⁻¹) * (q * (S.t * V.vN) * q⁻¹) by
        group, hdq] at h2
      exact mul_left_cancel h2
    have k1 := key _ (w₂_mem_Q0 _ _ _ _) (V.w₂_conj_E0 hdE)
    have k2 := key _ V.w₁N_mem_Q0 (V.w₁N_conj_E0 hdE)
    constructor
    · rw [show V.D.w₂ * (S.t * V.vN) * V.D.w₂⁻¹ = (V.D.w₂ * S.t * V.D.w₂⁻¹) *
        (V.D.w₂ * V.vN * V.D.w₂⁻¹) by group, V.w₂_conj_t, mul_assoc] at k1
      have k1' := mul_left_cancel k1
      calc V.D.w₂ * V.vN * V.D.w₂⁻¹ = V.yi * (V.yi * (V.D.w₂ * V.vN * V.D.w₂⁻¹)) := by
            rw [← mul_assoc, V.yi_sq, one_mul]
        _ = V.yi * V.vN := by rw [k1']
        _ = V.vN * V.yi := (V.vN_comm_E0 (yi_mem_E0 _ _)).symm
    · rw [show V.w₁N * (S.t * V.vN) * V.w₁N⁻¹ = (V.w₁N * S.t * V.w₁N⁻¹) *
        (V.w₁N * V.vN * V.w₁N⁻¹) by group, V.w₁N_conj_t, mul_assoc] at k2
      have k2' := mul_left_cancel k2
      calc V.w₁N * V.vN * V.w₁N⁻¹ = S.z * (S.z * (V.w₁N * V.vN * V.w₁N⁻¹)) := by
            rw [← mul_assoc, z_mul_z, one_mul]
        _ = S.z * V.vN := by rw [k2']
        _ = V.vN * S.z := (V.vN_comm_E0 (z_mem_E0 _ _)).symm

theorem C₁_cases : (∃ d ∈ zpowers V.ki, d * V.vN ∈ V.D.C₁) ∨
    (∃ d ∈ zpowers V.ki, d * (S.t * V.vN) ∈ V.D.C₁) := by
  obtain ⟨c, hc₁, hc⟩ : ∃ c ∈ V.D.C₁, c ∉ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) := by
    by_contra hne
    push Not at hne
    have hle : V.D.C₁ ⊔ zpowers S.t ≤ zpowers V.ki ⊔ zpowers S.t :=
      sup_le (fun c hc => hne c hc) le_sup_right
    rw [V.D.C₁_sup] at hle
    have := Subgroup.card_le_of_le hle
    rw [V.D.card_C, V.card_kt] at this
    norm_num at this
  have hcC : c ∈ closure ({S.t, V.ki, V.D.v} : Set X) := V.D.C_eq ▸ V.D.C₁_le hc₁
  rcases V.mem_C hcC with h | h
  · exact absurd h hc
  rcases mem_or_of_mem_sup V.elemAbelianTwo_ki S.t_sq
    (fun a ha => commute_of_mem_B t_mem_B (zpowers_le.mpr V.hki.mem ha)) h with h' | h'
  · exact Or.inl ⟨c * V.vN⁻¹, h', by rw [inv_mul_cancel_right]; exact hc₁⟩
  · refine Or.inr ⟨c * V.vN⁻¹ * S.t, h', ?_⟩
    rw [show c * V.vN⁻¹ * S.t * (S.t * V.vN) = c * V.vN⁻¹ * (S.t * S.t) * V.vN by group, t_mul_t,
      mul_one, inv_mul_cancel_right]
    exact hc₁

theorem ki_mem_Q0C1 {d : X} (hd : d ∈ zpowers V.ki) :
    d ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ ⊔ V.D.C₁ :=
  mem_sup_left (V.E0_le_Q0 (V.zk_le_E0 (mem_sup_right hd)))

theorem vN_mem_Q0C1 (h : V.D.w₂ * V.vN = V.vN * V.D.w₂) :
    V.vN ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ ⊔ V.D.C₁ := by
  rcases V.C₁_cases with ⟨d, hd, hc⟩ | ⟨d, hd, hc⟩
  · have : V.vN = d⁻¹ * (d * V.vN) := by group
    rw [this]
    exact mul_mem (V.ki_mem_Q0C1 (inv_mem hd)) (mem_sup_right hc)
  · exfalso
    have hcQ := V.D.C₁_comm _ hc V.D.w₂ (w₂_mem_Q0 _ _ _ _)
    have hdw : d * V.D.w₂ = V.D.w₂ * d := by
      have hdE : d ∈ S.E0 V.yi V.ki := V.zk_le_E0 (mem_sup_right hd)
      have := V.w₂_conj_E0 hdE
      calc d * V.D.w₂ = (V.D.w₂ * d * V.D.w₂⁻¹) * V.D.w₂ := by rw [this]
        _ = V.D.w₂ * d := by group
    have h1 : V.D.w₂ * S.t = S.t * V.D.w₂ := by
      have e1 : d * (S.t * V.vN) * V.D.w₂ = V.D.w₂ * (d * (S.t * V.vN)) := hcQ
      have e2 : d * (S.t * (V.vN * V.D.w₂)) = d * (V.D.w₂ * S.t * V.vN) := by
        calc d * (S.t * (V.vN * V.D.w₂)) = d * (S.t * V.vN) * V.D.w₂ := by group
          _ = V.D.w₂ * (d * (S.t * V.vN)) := e1
          _ = (V.D.w₂ * d) * (S.t * V.vN) := by group
          _ = (d * V.D.w₂) * (S.t * V.vN) := by rw [hdw]
          _ = d * (V.D.w₂ * S.t * V.vN) := by group
      have e3 := mul_left_cancel e2
      rw [← h, ← mul_assoc] at e3
      exact (mul_right_cancel e3).symm
    have h2 := V.w₂_conj_t
    rw [h1, mul_inv_cancel_right] at h2
    exact V.hyi.not_mem_B (by
      have : V.yi = S.t⁻¹ * (S.t * V.yi) := by group
      rw [this, ← h2, inv_mul_cancel]
      exact one_mem _)

theorem tvN_mem_Q0C1 (h : V.D.w₂ * V.vN * V.D.w₂⁻¹ = V.vN * V.yi) :
    S.t * V.vN ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ ⊔ V.D.C₁ := by
  rcases V.C₁_cases with ⟨d, hd, hc⟩ | ⟨d, hd, hc⟩
  · exfalso
    have hcQ := V.D.C₁_comm _ hc V.D.w₂ (w₂_mem_Q0 _ _ _ _)
    have hdw : V.D.w₂ * d * V.D.w₂⁻¹ = d :=
      V.w₂_conj_E0 (V.zk_le_E0 (mem_sup_right hd))
    have h1 : V.D.w₂ * (d * V.vN) * V.D.w₂⁻¹ = d * V.vN := by rw [← hcQ, mul_inv_cancel_right]
    rw [show V.D.w₂ * (d * V.vN) * V.D.w₂⁻¹ = (V.D.w₂ * d * V.D.w₂⁻¹) * (V.D.w₂ * V.vN * V.D.w₂⁻¹)
      by group, hdw, h] at h1
    have h3 : V.vN * V.yi = V.vN := mul_left_cancel h1
    have h4 : V.yi = 1 := mul_eq_left.mp h3
    exact V.hyi.not_mem_B (h4 ▸ one_mem _)
  · have : S.t * V.vN = d⁻¹ * (d * (S.t * V.vN)) := by group
    rw [this]
    exact mul_mem (V.ki_mem_Q0C1 (inv_mem hd)) (mem_sup_right hc)

end ISide

end Sec8

end CFSG.ComponentClassification.HSFLit
