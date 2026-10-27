module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2f

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem exists_qq : ∃ p : X × X, (p.1 ∈ C.S₂ ∧ act p.1 C.E₁ = C.G₁ ∧ act p.1 C.G₁ = C.E₁ ∧
    act p.1 C.G₂ = C.G₃ ∧ act p.1 C.G₃ = C.G₂ ∧ (∀ f ∈ C.Fv, p.1 * f * p.1⁻¹ = f) ∧
    p.1 ^ 2 ∈ C.E₀) ∧ (p.2 ∈ C.S₂ ∧ act p.2 C.E₁ = C.G₂ ∧ act p.2 C.G₂ = C.E₁ ∧
    act p.2 C.G₁ = C.G₃ ∧ act p.2 C.G₃ = C.G₁ ∧ (∀ f ∈ C.Fv, p.2 * f * p.2⁻¹ = f) ∧
    p.2 ^ 2 ∈ C.E₀) := by
  obtain ⟨a, ha, b, hb, ⟨a0, a1, a2, a3, aF, ha2⟩, ⟨b0, b2, b1, b3, bF, hb2⟩⟩ := C.exists_good
  have hvN : C.v' ∈ normalizer (C.E₀ : Set X) := C.normalizes_E0_of_mem_Q₁ C.v'_mem_Q₁
  have hvF : C.v' ∈ C.Fv := mem_sup_right (mem_zpowers _)
  obtain ⟨a', ha', a0', a1', a2', a3', aF', ha2'⟩ : ∃ a' ∈ C.S₂, act a' C.E₁ = C.G₁ ∧
      act a' C.G₁ = C.E₁ ∧ act a' C.G₂ = C.G₃ ∧ act a' C.G₃ = C.G₂ ∧
      (∀ f ∈ C.Fv, a' * f * a'⁻¹ = f) ∧ a' ^ 2 ∈ C.E₀ := by
    rcases mem_or_of_mem_sup_zpowers hvN C.v'_sq_mem_E0 ha2 with h | h
    · exact ⟨a, ha, a0, a1, a2, a3, aF, h⟩
    · have haN := C.S₂_le ha
      obtain ⟨-, -, c2⟩ := C.cong_q₁ haN a0 a1 a2
      obtain ⟨e₂, he₂, hew⟩ : ∃ e ∈ C.E₀, a * C.D₁.w₂ * a⁻¹ = e * (C.v' * C.D₁.w₂) :=
        ⟨_, C.cong_def.mp c2, by group⟩
      obtain ⟨e, he, hea⟩ : ∃ e ∈ C.E₀, a ^ 2 = e * C.v' := ⟨_, h, by group⟩
      refine ⟨a * C.D₁.w₂, mul_mem ha (C.S₁_le_S₂ (C.Q₁_le_S₁ C.w₂_mem_Q₁)), ?_, ?_, ?_, ?_,
        C.conj_Fv_mul aF C.w₂_mem_Q₁ C.w₂_v', ?_⟩
      · rw [act_mul, C.act_Q₁_E₁ C.w₂_mem_Q₁, a0]
      · rw [act_mul, C.act_Q₁ C.w₂_mem_Q₁ C.r₁_mem, a1]
      · rw [act_mul, C.act_Q₁ C.w₂_mem_Q₁ C.r₂_mem, a2]
      · rw [act_mul, C.act_Q₁ C.w₂_mem_Q₁ C.r₃_mem, a3]
      · have e1 : (a * C.D₁.w₂) ^ 2 = (a * C.D₁.w₂ * a⁻¹) * a ^ 2 * C.D₁.w₂ := by
          rw [pow_two, pow_two]; group
        have hc : C.v' * C.D₁.w₂ * e = e * (C.v' * C.D₁.w₂) :=
          (C.comm_E0_Q₁ he (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁)).symm
        rw [e1, hew, hea]
        have e2 : e₂ * (C.v' * C.D₁.w₂) * (e * C.v') * C.D₁.w₂ =
            e₂ * e * (C.v' * (C.D₁.w₂ * C.v') * C.D₁.w₂) := by
          calc e₂ * (C.v' * C.D₁.w₂) * (e * C.v') * C.D₁.w₂ =
                e₂ * (C.v' * C.D₁.w₂ * e) * C.v' * C.D₁.w₂ := by group
            _ = e₂ * (e * (C.v' * C.D₁.w₂)) * C.v' * C.D₁.w₂ := by rw [hc]
            _ = e₂ * e * (C.v' * (C.D₁.w₂ * C.v') * C.D₁.w₂) := by group
        rw [e2, C.w₂_v', ← mul_assoc C.v' C.v', C.v'v', one_mul, ← pow_two]
        exact mul_mem (mul_mem he₂ he) C.w₂_sq_mem
  obtain ⟨b', hb', b0', b2', b1', b3', bF', hb2'⟩ : ∃ b' ∈ C.S₂, act b' C.E₁ = C.G₂ ∧
      act b' C.G₂ = C.E₁ ∧ act b' C.G₁ = C.G₃ ∧ act b' C.G₃ = C.G₁ ∧
      (∀ f ∈ C.Fv, b' * f * b'⁻¹ = f) ∧ b' ^ 2 ∈ C.E₀ := by
    rcases mem_or_of_mem_sup_zpowers hvN C.v'_sq_mem_E0 hb2 with h | h
    · exact ⟨b, hb, b0, b2, b1, b3, bF, h⟩
    · have hbN := C.S₂_le hb
      obtain ⟨-, c1, -⟩ := C.cong_q₂ hbN b0 b1 b2
      obtain ⟨e₁, he₁, hew⟩ : ∃ e ∈ C.E₀, b * C.w₁' * b⁻¹ = e * (C.v' * C.w₁') :=
        ⟨_, C.cong_def.mp c1, by group⟩
      obtain ⟨e, he, heb⟩ : ∃ e ∈ C.E₀, b ^ 2 = e * C.v' := ⟨_, h, by group⟩
      refine ⟨b * C.w₁', mul_mem hb (C.S₁_le_S₂ (C.Q₁_le_S₁ C.w₁'_mem_Q₁)), ?_, ?_, ?_, ?_,
        C.conj_Fv_mul bF C.w₁'_mem_Q₁ C.w₁'_v', ?_⟩
      · rw [act_mul, C.act_Q₁_E₁ C.w₁'_mem_Q₁, b0]
      · rw [act_mul, C.act_Q₁ C.w₁'_mem_Q₁ C.r₂_mem, b2]
      · rw [act_mul, C.act_Q₁ C.w₁'_mem_Q₁ C.r₁_mem, b1]
      · rw [act_mul, C.act_Q₁ C.w₁'_mem_Q₁ C.r₃_mem, b3]
      · have e1 : (b * C.w₁') ^ 2 = (b * C.w₁' * b⁻¹) * b ^ 2 * C.w₁' := by
          rw [pow_two, pow_two]; group
        have hc : C.v' * C.w₁' * e = e * (C.v' * C.w₁') :=
          (C.comm_E0_Q₁ he (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁)).symm
        rw [e1, hew, heb]
        have e2 : e₁ * (C.v' * C.w₁') * (e * C.v') * C.w₁' =
            e₁ * e * (C.v' * (C.w₁' * C.v') * C.w₁') := by
          calc e₁ * (C.v' * C.w₁') * (e * C.v') * C.w₁' =
                e₁ * (C.v' * C.w₁' * e) * C.v' * C.w₁' := by group
            _ = e₁ * (e * (C.v' * C.w₁')) * C.v' * C.w₁' := by rw [hc]
            _ = e₁ * e * (C.v' * (C.w₁' * C.v') * C.w₁') := by group
        rw [e2, C.w₁'_v', ← mul_assoc C.v' C.v', C.v'v', one_mul, ← pow_two]
        exact mul_mem (mul_mem he₁ he) C.w₁'_sq_mem_E0
  exact ⟨(a', b'), ⟨ha', a0', a1', a2', a3', aF', ha2'⟩, ⟨hb', b0', b2', b1', b3', bF', hb2'⟩⟩

def qq : X × X := Classical.choose C.exists_qq

abbrev q₁ : X := C.qq.1

abbrev q₂ : X := C.qq.2

theorem q₁_spec : C.q₁ ∈ C.S₂ ∧ act C.q₁ C.E₁ = C.G₁ ∧ act C.q₁ C.G₁ = C.E₁ ∧
    act C.q₁ C.G₂ = C.G₃ ∧ act C.q₁ C.G₃ = C.G₂ ∧ (∀ f ∈ C.Fv, C.q₁ * f * C.q₁⁻¹ = f) ∧
    C.q₁ ^ 2 ∈ C.E₀ := (Classical.choose_spec C.exists_qq).1

theorem q₂_spec : C.q₂ ∈ C.S₂ ∧ act C.q₂ C.E₁ = C.G₂ ∧ act C.q₂ C.G₂ = C.E₁ ∧
    act C.q₂ C.G₁ = C.G₃ ∧ act C.q₂ C.G₃ = C.G₁ ∧ (∀ f ∈ C.Fv, C.q₂ * f * C.q₂⁻¹ = f) ∧
    C.q₂ ^ 2 ∈ C.E₀ := (Classical.choose_spec C.exists_qq).2

theorem q₁_mem : C.q₁ ∈ C.S₂ := C.q₁_spec.1

theorem q₂_mem : C.q₂ ∈ C.S₂ := C.q₂_spec.1

theorem q₁_N : C.q₁ ∈ normalizer (C.D₁.Q₁ : Set X) := C.S₂_le C.q₁_mem

theorem q₂_N : C.q₂ ∈ normalizer (C.D₁.Q₁ : Set X) := C.S₂_le C.q₂_mem

theorem q₁_F {f : X} (hf : f ∈ C.Fv) : C.q₁ * f * C.q₁⁻¹ = f := C.q₁_spec.2.2.2.2.2.1 f hf

theorem q₂_F {f : X} (hf : f ∈ C.Fv) : C.q₂ * f * C.q₂⁻¹ = f := C.q₂_spec.2.2.2.2.2.1 f hf

theorem q₁_E0 {e : X} (he : e ∈ C.E₀) : C.q₁ * e * C.q₁⁻¹ = e := C.q₁_F (mem_sup_left he)

theorem q₂_E0 {e : X} (he : e ∈ C.E₀) : C.q₂ * e * C.q₂⁻¹ = e := C.q₂_F (mem_sup_left he)

theorem q₁_cong : C.Cong (C.q₁ * S.t * C.q₁⁻¹) (S.t * C.v' * C.w₁') ∧
    C.Cong (C.q₁ * C.w₁' * C.q₁⁻¹) C.w₁' ∧ C.Cong (C.q₁ * C.D₁.w₂ * C.q₁⁻¹) (C.v' * C.D₁.w₂) :=
  C.cong_q₁ C.q₁_N C.q₁_spec.2.1 C.q₁_spec.2.2.1 C.q₁_spec.2.2.2.1

theorem q₂_cong : C.Cong (C.q₂ * S.t * C.q₂⁻¹) (S.t * C.v' * C.D₁.w₂) ∧
    C.Cong (C.q₂ * C.w₁' * C.q₂⁻¹) (C.v' * C.w₁') ∧ C.Cong (C.q₂ * C.D₁.w₂ * C.q₂⁻¹) C.D₁.w₂ :=
  C.cong_q₂ C.q₂_N C.q₂_spec.2.1 C.q₂_spec.2.2.2.1 C.q₂_spec.2.2.1

theorem q₁_t' : C.Cong (C.q₁ * S.t * C.q₁⁻¹) ((C.v' * C.w₁') * S.t) :=
  C.cong_trans C.q₁_cong.1 (by
    rw [mul_assoc S.t]; exact C.cong_comm C.t_mem_Q₁ (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁))

theorem q₂_t' : C.Cong (C.q₂ * S.t * C.q₂⁻¹) ((C.v' * C.D₁.w₂) * S.t) :=
  C.cong_trans C.q₂_cong.1 (by
    rw [mul_assoc S.t]; exact C.cong_comm C.t_mem_Q₁ (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁))

theorem Q₁_le_S₂ : C.D₁.Q₁ ≤ C.S₂ := C.Q₁_le_S₁.trans C.S₁_le_S₂

theorem mem_S₁_cases {s : X} (hs : s ∈ C.S₂) (h : act s C.E₁ = C.E₁) :
    s ∈ C.D₁.Q₁ ∨ s * C.D₁.u⁻¹ ∈ C.D₁.Q₁ := by
  have hS₁ : s ∈ C.D₁.S₁ := by
    rw [← C.S₂_inf]; exact ⟨hs, mem_normalizer_of_map_eq h⟩
  rw [C.S₁_eq_sup] at hS₁
  exact mem_or_of_mem_sup_zpowers C.u_normalizes (by rw [pow_two, C.u_mul_u]; exact one_mem _)
    hS₁

theorem mem_S₂_cases {s : X} (hs : s ∈ C.S₂) :
    ∃ w : X, (w = 1 ∨ w = C.q₁ ∨ w = C.q₂ ∨ w = C.q₁ * C.q₂) ∧
      (w⁻¹ * s ∈ C.D₁.Q₁ ∨ w⁻¹ * s * C.D₁.u⁻¹ ∈ C.D₁.Q₁) := by
  obtain ⟨-, a0, -, a2, -, -, -⟩ := C.q₁_spec
  obtain ⟨-, b0, -, -, -, -, -⟩ := C.q₂_spec
  have key : ∀ w ∈ C.S₂, act w C.E₁ = act s C.E₁ →
      w⁻¹ * s ∈ C.D₁.Q₁ ∨ w⁻¹ * s * C.D₁.u⁻¹ ∈ C.D₁.Q₁ := fun w hw h =>
    C.mem_S₁_cases (mul_mem (inv_mem hw) hs) (by rw [act_mul, ← h, ← act_mul, inv_mul_cancel,
      act_one_eq])
  rcases C.mem_Ω_iff.mp (C.act_mem_Ω (C.S₂_le hs) C.mem_Ω_E₁) with h | h | h | h
  · exact ⟨1, Or.inl rfl, key 1 (one_mem _) (by rw [act_one_eq, h])⟩
  · exact ⟨C.q₁, Or.inr (Or.inl rfl), key _ C.q₁_mem (by rw [a0, h])⟩
  · exact ⟨C.q₂, Or.inr (Or.inr (Or.inl rfl)), key _ C.q₂_mem (by rw [b0, h])⟩
  · exact ⟨C.q₁ * C.q₂, Or.inr (Or.inr (Or.inr rfl)), key _ (mul_mem C.q₁_mem C.q₂_mem)
      (by rw [act_mul, b0, a2, h])⟩

theorem W_F {w : X} (hw : w = 1 ∨ w = C.q₁ ∨ w = C.q₂ ∨ w = C.q₁ * C.q₂) {f : X}
    (hf : f ∈ C.Fv) : w * f * w⁻¹ = f := by
  rcases hw with rfl | rfl | rfl | rfl
  · group
  · exact C.q₁_F hf
  · exact C.q₂_F hf
  · rw [show C.q₁ * C.q₂ * f * (C.q₁ * C.q₂)⁻¹ = C.q₁ * (C.q₂ * f * C.q₂⁻¹) * C.q₁⁻¹ by group,
      C.q₂_F hf, C.q₁_F hf]

theorem Q₁_le_Tma_v'k : C.D₁.Q₁ ≤ C.Tma C.v' (zpowers C.F.kF) C.kpow_le_E0 := by
  have hb : ∀ {p : X}, p ∈ C.D₁.Q₁ → C.beta p ∈ zpowers C.F.kF →
      p ∈ C.Tma C.v' (zpowers C.F.kF) C.kpow_le_E0 := fun hp h =>
    C.mem_Tma.mpr ⟨fun e he => C.conj_eq_of_mem_Q₁ hp he, by rw [← C.beta_def]; exact h⟩
  rw [C.Q₁_eq]
  refine sup_le (sup_le (sup_le ?_ (zpowers_le.mpr (hb C.v'_mem_Q₁ (by
    rw [C.beta_v']; exact one_mem _)))) (zpowers_le.mpr (hb C.w₁'_mem_Q₁ (by
    rw [C.beta_w₁']; exact one_mem _)))) (zpowers_le.mpr (hb C.w₂_mem_Q₁ (by
    rw [C.beta_w₂]; exact one_mem _)))
  rw [C.E₁_eq]
  refine sup_le (fun e he => hb (C.E0_le_Q₁ he) (by rw [C.beta_of_mem_E0 he]; exact one_mem _))
    (zpowers_le.mpr (hb C.t_mem_Q₁ (by rw [C.beta_t]; exact mem_zpowers _)))

theorem Q₁_v' {a : X} (ha : a ∈ C.D₁.Q₁) : a * C.v' * a⁻¹ = C.v' ∨
    a * C.v' * a⁻¹ = C.F.kF * C.v' := by
  have h := (C.mem_Tma.mp (C.Q₁_le_Tma_v'k ha)).2
  rw [← C.beta_def] at h
  have e : a * C.v' * a⁻¹ = C.v' * C.beta a := by rw [C.beta_def]; group
  rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq h with h1 | h1 <;> rw [e, h1]
  · exact Or.inl (mul_one _)
  · exact Or.inr (C.comm_v'_E0 C.k_mem_E0)

theorem S₂_decomp {s : X} (hs : s ∈ C.S₂) : ∃ w a : X, (∀ f ∈ C.Fv, w * f * w⁻¹ = f) ∧
    a ∈ C.D₁.Q₁ ∧ (s = w * a ∨ s = w * a * C.D₁.u) := by
  obtain ⟨w, hw, h | h⟩ := C.mem_S₂_cases hs
  · exact ⟨w, w⁻¹ * s, fun f hf => C.W_F hw hf, h, Or.inl (by group)⟩
  · exact ⟨w, w⁻¹ * s * C.D₁.u⁻¹, fun f hf => C.W_F hw hf, h, Or.inr (by group)⟩

theorem u_k : C.D₁.u * C.F.kF * C.D₁.u⁻¹ = C.F.kF := conj_eq_of_comm (C.u_comm_B (kF_mem_B C.F))

theorem u_z : C.D₁.u * S.z * C.D₁.u⁻¹ = S.z := conj_eq_of_comm (C.u_comm_B z_mem_B)

theorem u_v' : C.D₁.u * C.v' * C.D₁.u⁻¹ = C.v' := conj_eq_of_comm C.u_comm_v'

theorem S₂_conj_of {s x x' : X} (hs : s ∈ C.S₂) (hx : x ∈ C.Fv)
    (hQ : ∀ a ∈ C.D₁.Q₁, a * x * a⁻¹ = x) (hu : C.D₁.u * x * C.D₁.u⁻¹ = x') (hx' : x' ∈ C.Fv)
    (hQ' : ∀ a ∈ C.D₁.Q₁, a * x' * a⁻¹ = x') :
    s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x' := by
  obtain ⟨w, a, hw, ha, rfl | rfl⟩ := C.S₂_decomp hs
  · left
    rw [show w * a * x * (w * a)⁻¹ = w * (a * x * a⁻¹) * w⁻¹ by group, hQ a ha, hw x hx]
  · right
    rw [show w * a * C.D₁.u * x * (w * a * C.D₁.u)⁻¹ =
      w * (a * (C.D₁.u * x * C.D₁.u⁻¹) * a⁻¹) * w⁻¹ by group, hu, hQ' a ha, hw x' hx']

theorem S₂_z {s : X} (hs : s ∈ C.S₂) : s * S.z * s⁻¹ = S.z := by
  have hQ : ∀ a ∈ C.D₁.Q₁, a * S.z * a⁻¹ = S.z := fun _ ha => C.conj_eq_of_mem_Q₁ ha C.z_mem_E0
  rcases C.S₂_conj_of hs (mem_sup_left C.z_mem_E0) hQ C.u_z (mem_sup_left C.z_mem_E0) hQ with
    h | h <;> exact h

theorem S₂_k {s : X} (hs : s ∈ C.S₂) : s * C.F.kF * s⁻¹ = C.F.kF := by
  have hQ : ∀ a ∈ C.D₁.Q₁, a * C.F.kF * a⁻¹ = C.F.kF := fun _ ha =>
    C.conj_eq_of_mem_Q₁ ha C.k_mem_E0
  rcases C.S₂_conj_of hs (mem_sup_left C.k_mem_E0) hQ C.u_k (mem_sup_left C.k_mem_E0) hQ with
    h | h <;> exact h

theorem S₂_y {s : X} (hs : s ∈ C.S₂) :
    s * C.F.yF * s⁻¹ = C.F.yF ∨ s * C.F.yF * s⁻¹ = S.z * C.F.yF :=
  C.S₂_conj_of hs (mem_sup_left C.y_mem_E0) (fun _ ha => C.conj_eq_of_mem_Q₁ ha C.y_mem_E0)
    C.u_y (mem_sup_left (mul_mem C.z_mem_E0 C.y_mem_E0))
    (fun _ ha => C.conj_eq_of_mem_Q₁ ha (mul_mem C.z_mem_E0 C.y_mem_E0))

theorem S₂_v' {s : X} (hs : s ∈ C.S₂) :
    s * C.v' * s⁻¹ = C.v' ∨ s * C.v' * s⁻¹ = C.F.kF * C.v' := by
  obtain ⟨w, a, hw, ha, rfl | rfl⟩ := C.S₂_decomp hs
  · rw [show w * a * C.v' * (w * a)⁻¹ = w * (a * C.v' * a⁻¹) * w⁻¹ by group]
    rcases C.Q₁_v' ha with h | h <;> rw [h]
    · exact Or.inl (hw _ (mem_sup_right (mem_zpowers _)))
    · exact Or.inr (hw _ (mul_mem (mem_sup_left C.k_mem_E0) (mem_sup_right (mem_zpowers _))))
  · rw [show w * a * C.D₁.u * C.v' * (w * a * C.D₁.u)⁻¹ =
      w * (a * (C.D₁.u * C.v' * C.D₁.u⁻¹) * a⁻¹) * w⁻¹ by group, C.u_v']
    rcases C.Q₁_v' ha with h | h <;> rw [h]
    · exact Or.inl (hw _ (mem_sup_right (mem_zpowers _)))
    · exact Or.inr (hw _ (mul_mem (mem_sup_left C.k_mem_E0) (mem_sup_right (mem_zpowers _))))

theorem Zz_le_E0 : C.Zz ≤ C.E₀ := C.zk_le_E0

theorem Zz_le_S₂ : C.Zz ≤ C.S₂ := C.Zz_le_E0.trans (C.E0_le_Q₁.trans C.Q₁_le_S₂)

theorem S₂_Zz {s : X} (hs : s ∈ C.S₂) {c : X} (hc : c ∈ C.Zz) : s * c * s⁻¹ = c :=
  C.fix_Zz (C.S₂_z hs) (C.S₂_k hs) hc

theorem mem_Zz_of_center {c : X} (hc : c ∈ C.S₂) (hcc : ∀ s ∈ C.S₂, c * s = s * c) :
    c ∈ C.Zz := by
  have hE₁ : c ∈ C.E₁ := mem_E_of_centralizes C.isRefl_y C.isPGroup_S₂ hc fun e he => by
    rw [hcc e (C.Q₁_le_S₂ (C.E₁_le_Q₁ he)), mul_inv_cancel_right]
  have hE : c ∈ C.E₀ := C.mem_E0_of_comm_v' hE₁ (hcc _ (C.Q₁_le_S₂ C.v'_mem_Q₁))
  exact C.mem_zk_of_mem_E0 hE (by rw [← hcc _ C.u_mem_S₂, mul_inv_cancel_right])

theorem comm_Fv_mem_Zz {s : X} (hs : s ∈ C.S₂) {f : X} (hf : f ∈ C.Fv) :
    s * f * s⁻¹ * f⁻¹ ∈ C.Zz := by
  let H : Subgroup X :=
    { carrier := {f | f ∈ C.Fv ∧ s * f * s⁻¹ * f⁻¹ ∈ C.Zz}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hc : a * (s * b * s⁻¹ * b⁻¹) = (s * b * s⁻¹ * b⁻¹) * a :=
          C.Fv_comm ha (mem_sup_left (C.Zz_le_E0 hb'))
        have e : s * (a * b) * s⁻¹ * (a * b)⁻¹ = (s * a * s⁻¹ * a⁻¹) * (s * b * s⁻¹ * b⁻¹) := by
          calc s * (a * b) * s⁻¹ * (a * b)⁻¹ =
                (s * a * s⁻¹ * a⁻¹) * (a * (s * b * s⁻¹ * b⁻¹)) * a⁻¹ := by group
            _ = (s * a * s⁻¹ * a⁻¹) * ((s * b * s⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [hc]
            _ = (s * a * s⁻¹ * a⁻¹) * (s * b * s⁻¹ * b⁻¹) := by group
        rw [e]
        exact mul_mem ha' hb'
      one_mem' := ⟨one_mem _, by rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have hc : a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ = (s * a * s⁻¹ * a⁻¹)⁻¹ * a⁻¹ :=
          C.Fv_comm (inv_mem ha) (mem_sup_left (inv_mem (C.Zz_le_E0 ha')))
        have e : s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = (s * a * s⁻¹ * a⁻¹)⁻¹ := by
          calc s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a := by group
            _ = (s * a * s⁻¹ * a⁻¹)⁻¹ * a⁻¹ * a := by rw [hc]
            _ = (s * a * s⁻¹ * a⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem ha' }
  have hzZ : S.z ∈ C.Zz := mem_sup_left (mem_zpowers _)
  have hkZ : C.F.kF ∈ C.Zz := mem_sup_right (mem_zpowers _)
  have hle : C.Fv ≤ H := by
    refine sup_le ?_ (zpowers_le.mpr ⟨mem_sup_right (mem_zpowers _), ?_⟩)
    · show closure {S.z, C.F.yF, C.F.kF} ≤ H
      rw [closure_le]
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact ⟨mem_sup_left C.z_mem_E0, by rw [C.S₂_z hs, mul_inv_cancel]; exact one_mem _⟩
      · refine ⟨mem_sup_left C.y_mem_E0, ?_⟩
        rcases C.S₂_y hs with h | h <;> rw [h]
        · rw [mul_inv_cancel]; exact one_mem _
        · rw [mul_inv_cancel_right]; exact hzZ
      · exact ⟨mem_sup_left C.k_mem_E0, by rw [C.S₂_k hs, mul_inv_cancel]; exact one_mem _⟩
    · rcases C.S₂_v' hs with h | h <;> rw [h]
      · rw [mul_inv_cancel]; exact one_mem _
      · rw [mul_inv_cancel_right]; exact hkZ
  exact (hle hf).2

theorem mem_Fv_of_Z₂ {a : X} (ha : a ∈ C.S₂) (h : ∀ s ∈ C.S₂, a * s * a⁻¹ * s⁻¹ ∈ C.Zz) :
    a ∈ C.Fv := by
  have haN := C.S₂_le ha
  have hfixA : ∀ {r : X}, r ∈ C.D₁.Q₁ →
      act a (C.E₀ ⊔ zpowers r) = C.E₀ ⊔ zpowers r := fun {r} hr => by
    rw [act, C.map_sup_zpowers haN]
    exact C.sup_zpowers_eq_of_coset (C.Zz_le_E0 (h r (C.Q₁_le_S₂ hr)))
  have haQ : a ∈ C.D₁.Q₁ := C.mem_Q₁_of_fix ha (by rw [C.E₁_eq]; exact hfixA C.t_mem_Q₁)
    (hfixA C.r₂_mem)
  have hcong : ∀ {q : X}, q ∈ C.S₂ → C.Cong (q * a * q⁻¹) a := fun {q} hq => by
    refine C.cong_def.mpr ?_
    rw [show q * a * q⁻¹ * a⁻¹ = (a * q * a⁻¹ * q⁻¹)⁻¹ by group]
    exact inv_mem (C.Zz_le_E0 (h q hq))
  have hv := C.comm_of_cong C.q₁_N (fun _ he => C.q₁_E0 he) haQ (hcong C.q₁_mem) C.w₂_mem_Q₁
    C.v'_mem_Q₁ C.q₁_cong.2.2
  have hvw₁ := C.comm_of_cong C.q₁_N (fun _ he => C.q₁_E0 he) haQ (hcong C.q₁_mem) C.t_mem_Q₁
    (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁) C.q₁_t'
  have hvw₂ := C.comm_of_cong C.q₂_N (fun _ he => C.q₂_E0 he) haQ (hcong C.q₂_mem) C.t_mem_Q₁
    (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁) C.q₂_t'
  have hw₁ : a * C.w₁' = C.w₁' * a := by
    have : C.v' * (a * C.w₁') = C.v' * (C.w₁' * a) := by
      rw [← mul_assoc, ← hv, mul_assoc, hvw₁, mul_assoc]
    exact mul_left_cancel this
  have hw₂ : a * C.D₁.w₂ = C.D₁.w₂ * a := by
    have : C.v' * (a * C.D₁.w₂) = C.v' * (C.D₁.w₂ * a) := by
      rw [← mul_assoc, ← hv, mul_assoc, hvw₂, mul_assoc]
    exact mul_left_cancel this
  rcases C.mem_A₁_cases haQ hv hw₁ with h' | h'
  · exact h'
  · exfalso
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, a = f * C.w₁' := ⟨_, h', by group⟩
    exact C.w₁'_w₂_ne (comm_of_mul_comm (C.Fv_comm_w₂ hf) hw₂)

theorem conj_mem_S₂ {h : X} (hh : h ∈ normalizer (C.S₂ : Set X)) {s : X} (hs : s ∈ C.S₂) :
    h⁻¹ * s * h ∈ C.S₂ := by
  have := (mem_normalizer_iff.mp (inv_mem hh) s).mp hs
  rwa [inv_inv] at this

theorem conj_Zz {h : X} (hh : h ∈ normalizer (C.S₂ : Set X)) {c : X} (hc : c ∈ C.Zz) :
    h * c * h⁻¹ ∈ C.Zz := by
  refine C.mem_Zz_of_center ((mem_normalizer_iff.mp hh c).mp (C.Zz_le_S₂ hc)) fun s hs => ?_
  have h1 := C.S₂_Zz (C.conj_mem_S₂ hh hs) hc
  calc h * c * h⁻¹ * s = h * (c * (h⁻¹ * s * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * s * h) * c) * h⁻¹ := by
        rw [show c * (h⁻¹ * s * h) = (h⁻¹ * s * h) * c by
          calc c * (h⁻¹ * s * h) = (h⁻¹ * s * h) * c * (h⁻¹ * s * h)⁻¹ * (h⁻¹ * s * h) := by
                rw [h1]
            _ = (h⁻¹ * s * h) * c := by group]
    _ = s * (h * c * h⁻¹) := by group

theorem conj_Fv' {h : X} (hh : h ∈ normalizer (C.S₂ : Set X)) {f : X} (hf : f ∈ C.Fv) :
    h * f * h⁻¹ ∈ C.Fv := by
  have hfS : f ∈ C.S₂ := C.Q₁_le_S₂ (C.Fv_le_Q₁ hf)
  refine C.mem_Fv_of_Z₂ ((mem_normalizer_iff.mp hh f).mp hfS) fun s hs => ?_
  have hs' := C.conj_mem_S₂ hh hs
  have h1 : f * (h⁻¹ * s * h) * f⁻¹ * (h⁻¹ * s * h)⁻¹ ∈ C.Zz := by
    rw [show f * (h⁻¹ * s * h) * f⁻¹ * (h⁻¹ * s * h)⁻¹ =
      ((h⁻¹ * s * h) * f * (h⁻¹ * s * h)⁻¹ * f⁻¹)⁻¹ by group]
    exact inv_mem (C.comm_Fv_mem_Zz hs' hf)
  have h2 := C.conj_Zz hh h1
  rwa [show h * (f * (h⁻¹ * s * h) * f⁻¹ * (h⁻¹ * s * h)⁻¹) * h⁻¹ =
    h * f * h⁻¹ * s * (h * f * h⁻¹)⁻¹ * s⁻¹ by group] at h2

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
