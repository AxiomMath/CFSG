module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Split

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

theorem z_mul_z : S.z * S.z = 1 := by rw [← pow_two, z_sq]

theorem t_mul_t : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]

theorem refl_x_conj {a : X} (h : IsRefl F a) : F.xF * a * F.xF⁻¹ = S.z * a := by
  have h1 : a * F.xF = F.xF⁻¹ * a := by rw [← h.inv]; group
  have h2 : F.xF⁻¹ * F.xF⁻¹ = S.z := by
    rw [← mul_inv_rev, ← pow_two, F.xF_sq, inv_eq_iff_mul_eq_one, ← pow_two, z_sq]
  calc F.xF * a * F.xF⁻¹ = F.xF * (a * F.xF) * F.xF⁻¹ * F.xF⁻¹ := by group
    _ = F.xF * (F.xF⁻¹ * a) * F.xF⁻¹ * F.xF⁻¹ := by rw [h1]
    _ = a * (F.xF⁻¹ * F.xF⁻¹) := by group
    _ = S.z * a := by rw [h2, (S.central_of_mem_B z_mem_B h.mem_T).symm]

theorem refl_xmul_sq {a : X} (h : IsRefl F a) : (F.xF * a) ^ 2 = 1 := by
  have h1 : a * F.xF = F.xF⁻¹ * a := by rw [← h.inv]; group
  rw [pow_two, show F.xF * a * (F.xF * a) = F.xF * (a * F.xF) * a by group, h1,
    show F.xF * (F.xF⁻¹ * a) * a = a * a by group, ← pow_two, h.sq]

theorem refl_xmul {a : X} (h : IsRefl F a) : IsRefl F (F.xF * a) := by
  refine ⟨mul_mem F.xF_mem h.mem, refl_xmul_sq h, ?_⟩
  calc F.xF * a * F.xF * (F.xF * a)⁻¹ = F.xF * (a * F.xF * a⁻¹) * F.xF⁻¹ := by group
    _ = F.xF⁻¹ := by rw [h.inv]; group

structure VSide (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  yi : X
  ki : X
  ui : X
  hyi : IsRefl F yi
  hki : IsK (S := S) ki
  hui : ui = F.xF * yi
  D : S.Sec6 T₁ yi ki ui
  hq : D.q0 = .extraspecial
  hu : D.u = S.t * ui

namespace VSide

variable (V : VSide S F T₁)

theorem act : S.ActHolds V.yi V.ki V.D.v V.D.w₁ V.D.w₂ .two := act_two_of_q0 V.D V.hq

theorem ki_sq : V.ki * V.ki = 1 := by rw [← pow_two, V.hki.sq]

theorem ki_inv : V.ki⁻¹ = V.ki := by rw [inv_eq_iff_mul_eq_one, V.ki_sq]

theorem ki_comm {g : X} (hg : g ∈ S.data.T) : V.ki * g = g * V.ki :=
  S.central_of_mem_B V.hki.mem hg

theorem v_conj_yi : V.D.v * V.yi * V.D.v⁻¹ = V.yi := v_conj_E0 V.D (yi_mem_E0 _ _)

theorem v_conj_x : V.D.v * F.xF * V.D.v⁻¹ = V.ki * F.xF := by
  have hc := u_comm_v V.D
  rw [V.hu] at hc
  simp only [V.hui] at hc
  have h1 : V.D.v * (S.t * (F.xF * V.yi)) * V.D.v⁻¹ = S.t * (F.xF * V.yi) := by
    rw [← hc]; group
  have h2 : V.D.v * (S.t * (F.xF * V.yi)) * V.D.v⁻¹ =
      (V.D.v * S.t * V.D.v⁻¹) * (V.D.v * F.xF * V.D.v⁻¹) * (V.D.v * V.yi * V.D.v⁻¹) := by
    group
  rw [h2, v_conj_t V.D, V.v_conj_yi] at h1
  have h3 : S.t * V.ki * (V.D.v * F.xF * V.D.v⁻¹) = S.t * F.xF := mul_right_cancel
    (by rw [h1, mul_assoc])
  calc V.D.v * F.xF * V.D.v⁻¹ = V.ki * (S.t⁻¹ * (S.t * V.ki * (V.D.v * F.xF * V.D.v⁻¹))) := by
        rw [show S.t⁻¹ * (S.t * V.ki * (V.D.v * F.xF * V.D.v⁻¹)) =
          V.ki * (V.D.v * F.xF * V.D.v⁻¹) by group, ← mul_assoc, V.ki_sq, one_mul]
    _ = V.ki * F.xF := by rw [h3]; group

theorem ki_mem_zk : V.ki ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) :=
  mem_sup_right (mem_zpowers _)

theorem z_mem_zk : S.z ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) :=
  mem_sup_left (mem_zpowers _)

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

theorem t_not_mem_zk : S.t ∉ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  intro h
  have h' : S.t ∈ S.E0 V.yi V.ki := by
    rw [E0_eq]; exact mem_sup_left h
  exact V.hyi.t_not_mem_E0 V.hki h'

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

theorem v_conj_zk {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    V.D.v * c * V.D.v⁻¹ = c := v_conj_E0 V.D (by rw [E0_eq]; exact mem_sup_left hc)

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

theorem v_mem_S₁ : V.D.v ∈ V.D.S₁ := V.D.T₁_le (v_mem_T₁ V.D)

theorem w₁_mem_S₁ : V.D.w₁ ∈ V.D.S₁ := V.D.T₁_le (w₁_mem_T₁ V.D)

theorem v_mem_C : V.D.v ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X) :=
  V.D.C_eq ▸ subset_closure (by simp)

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

theorem yi_inv : V.yi⁻¹ = V.yi := by rw [inv_eq_iff_mul_eq_one, ← pow_two, V.hyi.sq]

theorem yi_not_comm_xyi : V.yi * (F.xF * V.yi) ≠ F.xF * V.yi * V.yi := by
  intro h
  have h1 : V.yi * (F.xF * V.yi) = F.xF⁻¹ := by
    rw [← V.hyi.inv, V.yi_inv]; group
  have h2 : F.xF * V.yi * V.yi = F.xF := by rw [mul_assoc, ← pow_two, V.hyi.sq, mul_one]
  rw [h1, h2] at h
  exact xF_ne_inv F h.symm

theorem xyi_mem_T : F.xF * V.yi ∈ S.data.T := mul_mem (xF_mem_T F) V.hyi.mem_T

theorem v_sq_comm_xyi : V.D.v ^ 2 * (F.xF * V.yi) = F.xF * V.yi * V.D.v ^ 2 := by
  have hcu : V.D.v ^ 2 * V.D.u = V.D.u * V.D.v ^ 2 := by
    rw [pow_two, mul_assoc, ← u_comm_v V.D, ← mul_assoc, ← u_comm_v V.D, mul_assoc]
  rw [V.hu] at hcu
  simp only [V.hui] at hcu
  have ht := V.v_sq_comm_t
  calc V.D.v ^ 2 * (F.xF * V.yi) = S.t⁻¹ * (S.t * V.D.v ^ 2) * (F.xF * V.yi) := by group
    _ = S.t⁻¹ * (V.D.v ^ 2 * S.t) * (F.xF * V.yi) := by rw [ht]
    _ = S.t⁻¹ * (V.D.v ^ 2 * (S.t * (F.xF * V.yi))) := by group
    _ = S.t⁻¹ * (S.t * (F.xF * V.yi) * V.D.v ^ 2) := by rw [hcu]
    _ = F.xF * V.yi * V.D.v ^ 2 := by group

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
    have h1 := S.central_of_mem_B hcB V.xyi_mem_T
    have h2 := V.v_sq_comm_xyi
    rw [hv2] at h2
    apply V.yi_not_comm_xyi
    refine mul_left_cancel (a := c) ?_
    calc c * (V.yi * (F.xF * V.yi)) = (c * V.yi) * (F.xF * V.yi) := by group
      _ = (F.xF * V.yi) * (c * V.yi) := h2
      _ = (F.xF * V.yi * c) * V.yi := by group
      _ = (c * (F.xF * V.yi)) * V.yi := by rw [h1]
      _ = c * (F.xF * V.yi * V.yi) := by group

theorem conj_zk_of_fix {g : X} (hz : g * S.z * g⁻¹ = S.z) (hk : g * V.ki * g⁻¹ = V.ki) {c : X}
    (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) : g * c * g⁻¹ = c := by
  rcases V.eq_of_mem_zk hc with rfl | rfl | rfl | rfl
  · group
  · exact hz
  · exact hk
  · rw [show g * (S.z * V.ki) * g⁻¹ = (g * S.z * g⁻¹) * (g * V.ki * g⁻¹) by group, hz, hk]

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
  ·
    have hvT : V.D.v ∈ S.data.T := by
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

theorem t_comm_T {g : X} (hg : g ∈ S.data.T) : S.t * g = g * S.t := (S.data.commute_t hg).symm

theorem t_conj_T {g : X} (hg : g ∈ S.data.T) : S.t * g * S.t⁻¹ = g := by
  rw [t_comm_T hg, mul_inv_cancel_right]

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
    have htk : S.t * V.ki = V.ki * S.t := (commute_of_mem_B t_mem_B V.hki.mem)
    calc (V.D.v * S.t) ^ 2 = (V.D.v * S.t * V.D.v⁻¹) * V.D.v ^ 2 * S.t := by
          rw [pow_two, pow_two]; group
      _ = 1 := by
        rw [ht, hk, mul_assoc S.t, V.ki_sq, mul_one, ← pow_two, S.t_sq]

theorem vN_conj_T_of_conj {g : X} (hg : g ∈ S.data.T) :
    V.vN * g * V.vN⁻¹ = V.D.v * g * V.D.v⁻¹ := by
  unfold vN
  split_ifs
  · rfl
  · rw [show V.D.v * S.t * g * (V.D.v * S.t)⁻¹ = V.D.v * (S.t * g * S.t⁻¹) * V.D.v⁻¹ by group,
      t_conj_T hg]

theorem vN_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.vN * e * V.vN⁻¹ = e := by
  rw [V.vN_conj_T_of_conj (V.hyi.E_le_T (E0_le_E V.hki V.yi he)), v_conj_E0 V.D he]

theorem vN_conj_t : V.vN * S.t * V.vN⁻¹ = S.t * V.ki := by
  rw [V.vN_conj_T_of_conj S.data.t_mem_T, v_conj_t V.D]

theorem vN_conj_x : V.vN * F.xF * V.vN⁻¹ = V.ki * F.xF := by
  rw [V.vN_conj_T_of_conj (xF_mem_T F), V.v_conj_x]

theorem u_mem_T : V.D.u ∈ S.data.T := by
  rw [V.hu]
  simp only [V.hui]
  exact mul_mem S.data.t_mem_T V.xyi_mem_T

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

theorem vN_mem_T₁ : V.vN ∈ T₁ := by
  unfold vN
  split_ifs
  · exact v_mem_T₁ V.D
  · exact mul_mem (v_mem_T₁ V.D) (V.D.T₁_eq.symm.le (mem_sup_left (mem_sup_left
      S.data.t_mem_T)))

theorem vN_mem_S₁ : V.vN ∈ V.D.S₁ := V.D.T₁_le V.vN_mem_T₁

theorem w₁_conj_z : V.D.w₁ * S.z * V.D.w₁⁻¹ = S.z := V.act.2.2.2.2.1

theorem w₁_conj_ki : V.D.w₁ * V.ki * V.D.w₁⁻¹ = V.ki := V.act.2.2.2.2.2.2.2.2.1

theorem w₁_conj_t : V.D.w₁ * S.t * V.D.w₁⁻¹ = S.t * S.z * V.ki := V.act.2.2.1

theorem w₁_conj_yi : V.D.w₁ * V.yi * V.D.w₁⁻¹ = V.yi * V.ki := V.act.2.2.2.2.2.2.2.1

theorem w₁_sq : V.D.w₁ ^ 2 = 1 := by
  have h := V.D.q0_holds
  rw [V.hq] at h
  exact h.1

theorem w₂_sq : V.D.w₂ ^ 2 = 1 := by
  have h := V.D.q0_holds
  rw [V.hq] at h
  exact h.2.1

theorem w₁_conj_B {b : X} (hb : b ∈ S.B) :
    V.D.w₁ * b * V.D.w₁⁻¹ = b ∨ V.D.w₁ * b * V.D.w₁⁻¹ = b * (S.z * V.ki) := by
  rcases V.mem_B_cases hb with h | h
  · exact Or.inl (V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki h)
  · right
    have hb' : b = b * S.t * S.t := by rw [mul_assoc, ← pow_two, S.t_sq, mul_one]
    calc V.D.w₁ * b * V.D.w₁⁻¹ =
        (V.D.w₁ * (b * S.t) * V.D.w₁⁻¹) * (V.D.w₁ * S.t * V.D.w₁⁻¹) := by
          nth_rewrite 1 [hb']; group
      _ = (b * S.t) * (S.t * S.z * V.ki) := by
          rw [V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki h, V.w₁_conj_t]
      _ = b * (S.t * S.t) * (S.z * V.ki) := by group
      _ = b * (S.z * V.ki) := by rw [← pow_two, S.t_sq, mul_one]

theorem vN_conj_z : V.vN * S.z * V.vN⁻¹ = S.z := V.vN_conj_E0 (z_mem_E0 _ _)

theorem vN_conj_ki : V.vN * V.ki * V.vN⁻¹ = V.ki := V.vN_conj_E0 (ki_mem_E0 _ _)

theorem vN_conj_yi : V.vN * V.yi * V.vN⁻¹ = V.yi := V.vN_conj_E0 (yi_mem_E0 _ _)

theorem vN_conj_of_zk {b : X} (h : b ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    V.vN * b * V.vN⁻¹ = b := V.conj_zk_of_fix V.vN_conj_z V.vN_conj_ki h

theorem vN_conj_of_t {b : X} (h : b * S.t ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    V.vN * b * V.vN⁻¹ = b * V.ki := by
  have hb' : b = b * S.t * S.t := by rw [mul_assoc, t_mul_t, mul_one]
  calc V.vN * b * V.vN⁻¹ = (V.vN * (b * S.t) * V.vN⁻¹) * (V.vN * S.t * V.vN⁻¹) := by
        nth_rewrite 1 [hb']; group
    _ = (b * S.t) * (S.t * V.ki) := by rw [V.vN_conj_of_zk h, V.vN_conj_t]
    _ = b * (S.t * S.t) * V.ki := by group
    _ = b * V.ki := by rw [t_mul_t, mul_one]

theorem vN_conj_B {b : X} (hb : b ∈ S.B) :
    V.vN * b * V.vN⁻¹ = b ∨ V.vN * b * V.vN⁻¹ = b * V.ki := by
  rcases V.mem_B_cases hb with h | h
  · exact Or.inl (V.vN_conj_of_zk h)
  · exact Or.inr (V.vN_conj_of_t h)

theorem vN_mem_C : V.vN ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X) :=
  V.D.C_eq ▸ V.vN_mem_closure

theorem w₂_conj_t : V.D.w₂ * S.t * V.D.w₂⁻¹ = S.t * V.yi * V.ki := V.act.2.2.2.1

theorem w₂_conj_yi : V.D.w₂ * V.yi * V.D.w₂⁻¹ = V.yi := V.act.2.2.2.2.2.1

theorem w₂_conj_z : V.D.w₂ * S.z * V.D.w₂⁻¹ = S.z * V.ki := V.act.2.2.2.2.2.2.1

theorem w₂_conj_ki : V.D.w₂ * V.ki * V.D.w₂⁻¹ = V.ki := V.act.2.2.2.2.2.2.2.2.2

theorem act_eq : V.D.act = .two := by
  have h := V.D.act_holds
  cases hact : V.D.act
  · exfalso
    rw [hact] at h
    have h1 := h.2.2.1
    rw [V.w₁_conj_t] at h1
    exact V.hki.ne_one (mul_eq_left.mp h1)
  · rfl

theorem w₁_comm_C {c : X} (hc : c ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X)) :
    V.D.w₁ * c * V.D.w₁⁻¹ * c⁻¹ = 1 ∨ V.D.w₁ * c * V.D.w₁⁻¹ * c⁻¹ = S.z * V.ki := by
  have h := V.D.w₁_comm_C c hc
  rw [V.act_eq] at h
  change _ ∈ closure {S.z * V.ki} at h
  rw [← zpowers_eq_closure] at h
  exact eq_one_or_eq_of_mem_zpowers (S.sq_of_mem_B (mul_mem z_mem_B V.hki.mem)) h

theorem w₁_inv : V.D.w₁⁻¹ = V.D.w₁ := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, V.w₁_sq]

theorem w₂_inv : V.D.w₂⁻¹ = V.D.w₂ := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, V.w₂_sq]

theorem vN_inv : V.vN⁻¹ = V.vN := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, V.vN_sq]

theorem yi_mul_yi : V.yi * V.yi = 1 := by rw [← pow_two, V.hyi.sq]

theorem u_eq : V.D.u = S.t * (F.xF * V.yi) := by rw [V.hu, V.hui]

theorem u_mul_u : V.D.u * V.D.u = 1 := by
  rw [V.u_eq]
  have h1 := t_comm_T V.xyi_mem_T
  calc S.t * (F.xF * V.yi) * (S.t * (F.xF * V.yi)) =
      (S.t * S.t) * ((F.xF * V.yi) * (F.xF * V.yi)) := by
        rw [show S.t * (F.xF * V.yi) * (S.t * (F.xF * V.yi)) =
          S.t * ((F.xF * V.yi) * S.t) * (F.xF * V.yi) by group, ← h1]; group
    _ = 1 := by rw [t_mul_t, ← pow_two, refl_xmul_sq V.hyi, one_mul]

theorem u_inv : V.D.u⁻¹ = V.D.u := inv_eq_of_mul_eq_one_right V.u_mul_u

end VSide

end Sec8

end CFSG.ComponentClassification.HSFLit
