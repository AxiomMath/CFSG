module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2c

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem comm_eq_one {x g : X} (h : x * g * x⁻¹ * g⁻¹ = 1) : x * g = g * x := by
  calc x * g = x * g * x⁻¹ * g⁻¹ * (g * x) := by group
    _ = g * x := by rw [h, one_mul]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem comm_mul_right {x a b : X} (hx : x ∈ C.D₁.Q₁) (ha : a ∈ C.D₁.Q₁) (hb : b ∈ C.D₁.Q₁) :
    x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by
  rw [show x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹)
    by group, C.conj_eq_of_mem_Q₁ ha (C.comm_mem_E0 hx hb)]

theorem comm_E0_mul {x e a : X} (hx : x ∈ C.D₁.Q₁) (he : e ∈ C.E₀) (ha : a ∈ C.D₁.Q₁) :
    x * (e * a) * x⁻¹ * (e * a)⁻¹ = x * a * x⁻¹ * a⁻¹ := by
  rw [C.comm_mul_right hx (C.E0_le_Q₁ he) ha, C.conj_eq_of_mem_Q₁ hx he, mul_inv_cancel, one_mul]

theorem comm_conj_eq {n x g : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X))
    (hnE : ∀ e ∈ C.E₀, n * e * n⁻¹ = e) (hx : x ∈ C.D₁.Q₁) (hxc : C.Cong (n * x * n⁻¹) x)
    (hg : g ∈ C.D₁.Q₁) :
    x * g * x⁻¹ * g⁻¹ = x * (n * g * n⁻¹) * x⁻¹ * (n * g * n⁻¹)⁻¹ := by
  have hc := C.comm_mem_E0 hx hg
  have h1 := hnE _ hc
  rw [show n * (x * g * x⁻¹ * g⁻¹) * n⁻¹ =
    (n * x * n⁻¹) * (n * g * n⁻¹) * (n * x * n⁻¹)⁻¹ * (n * g * n⁻¹)⁻¹ by group] at h1
  obtain ⟨e, he, hex⟩ : ∃ e ∈ C.E₀, n * x * n⁻¹ = e * x :=
    ⟨n * x * n⁻¹ * x⁻¹, C.cong_def.mp hxc, by group⟩
  rw [hex] at h1
  have hh := C.conj_mem_Q₁ hn hg
  rw [← h1, show e * x * (n * g * n⁻¹) * (e * x)⁻¹ * (n * g * n⁻¹)⁻¹ =
    e * (x * (n * g * n⁻¹) * x⁻¹) * e⁻¹ * (n * g * n⁻¹)⁻¹ by group,
    conj_eq_of_comm (C.comm_E0_Q₁ he (C.conj_mem_Q₁ (le_normalizer hx) hh))]

theorem comm_of_cong {n x g a : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X))
    (hnE : ∀ e ∈ C.E₀, n * e * n⁻¹ = e) (hx : x ∈ C.D₁.Q₁) (hxc : C.Cong (n * x * n⁻¹) x)
    (hg : g ∈ C.D₁.Q₁) (ha : a ∈ C.D₁.Q₁) (hc : C.Cong (n * g * n⁻¹) (a * g)) :
    x * a = a * x := by
  have h := C.comm_conj_eq hn hnE hx hxc hg
  obtain ⟨e, he, hex⟩ : ∃ e ∈ C.E₀, n * g * n⁻¹ = e * (a * g) :=
    ⟨n * g * n⁻¹ * (a * g)⁻¹, C.cong_def.mp hc, by group⟩
  rw [hex, C.comm_E0_mul hx he (mul_mem ha hg), C.comm_mul_right hx ha hg] at h
  refine comm_eq_one ?_
  calc x * a * x⁻¹ * a⁻¹ = (x * a * x⁻¹ * a⁻¹) * (x * g * x⁻¹ * g⁻¹) *
        (x * g * x⁻¹ * g⁻¹)⁻¹ := by group
    _ = 1 := by rw [← h, mul_inv_cancel]

theorem P₃_le_Q₁ : C.P₃ ≤ C.D₁.Q₁ := by rw [C.Q₁_eq]; exact le_sup_left

theorem P₂_le_Q₁ : C.P₂ ≤ C.D₁.Q₁ := le_sup_left.trans C.P₃_le_Q₁

theorem mem_Fv_of_mem_E₁ {p : X} (hp : p ∈ C.E₁) (hβ : C.beta p = 1) : p ∈ C.E₀ :=
  C.mem_E0_of_comm_v' hp (C.beta_eq_one_iff.mp hβ)

theorem mem_Fv_of_mem_P₂ {p : X} (hp : p ∈ C.P₂) (hβ : C.beta p = 1) : p ∈ C.Fv := by
  rcases mem_or_of_mem_sup_zpowers C.v'_normalizes_E₁ C.v'_sq_mem hp with h | h
  · exact mem_sup_left (C.mem_Fv_of_mem_E₁ h hβ)
  · have hpQ : p ∈ C.D₁.Q₁ := C.P₂_le_Q₁ hp
    have hβ' : C.beta (p * C.v'⁻¹) = 1 := by
      rw [C.beta_mul hpQ (inv_mem C.v'_mem_Q₁), C.beta_inv C.v'_mem_Q₁, hβ, C.beta_v', inv_one,
        mul_one]
    rw [show p = p * C.v'⁻¹ * C.v' by group]
    exact mul_mem (mem_sup_left (C.mem_Fv_of_mem_E₁ h hβ')) (mem_sup_right (mem_zpowers _))

theorem mem_Fv_cases_P₃ {p : X} (hp : p ∈ C.P₃) (hβ : C.beta p = 1) :
    p ∈ C.Fv ∨ p * C.w₁'⁻¹ ∈ C.Fv := by
  rcases mem_or_of_mem_sup_zpowers C.w₁'_normalizes_P₂ (C.E0_le_P₂ C.w₁'_sq_mem_E0) hp with h | h
  · exact Or.inl (C.mem_Fv_of_mem_P₂ h hβ)
  · have hpQ : p ∈ C.D₁.Q₁ := C.P₃_le_Q₁ hp
    refine Or.inr (C.mem_Fv_of_mem_P₂ h ?_)
    rw [C.beta_mul hpQ (inv_mem C.w₁'_mem_Q₁), C.beta_inv C.w₁'_mem_Q₁, hβ, C.beta_w₁', inv_one,
      mul_one]

theorem mem_B_cases {x : X} (hx : x ∈ C.D₁.Q₁) (hxv : x * C.v' = C.v' * x) :
    x ∈ C.Fv ∨ x * C.w₁'⁻¹ ∈ C.Fv ∨ x * C.D₁.w₂⁻¹ ∈ C.Fv ∨
      x * (C.w₁' * C.D₁.w₂)⁻¹ ∈ C.Fv := by
  have hβ : C.beta x = 1 := C.beta_eq_one_iff.mpr hxv
  have hx' := hx
  rw [C.Q₁_eq] at hx'
  rcases mem_or_of_mem_sup_zpowers C.w₂_normalizes_P₃ (C.E0_le_P₃ C.w₂_sq_mem) hx' with h | h
  · rcases C.mem_Fv_cases_P₃ h hβ with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have hβ' : C.beta (x * C.D₁.w₂⁻¹) = 1 := by
      rw [C.beta_mul hx (inv_mem C.w₂_mem_Q₁), C.beta_inv C.w₂_mem_Q₁, hβ, C.beta_w₂, inv_one,
        mul_one]
    rcases C.mem_Fv_cases_P₃ h hβ' with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rwa [mul_inv_rev, ← mul_assoc]

theorem Fv_le_Q₁ : C.Fv ≤ C.D₁.Q₁ := sup_le C.E0_le_Q₁ (zpowers_le.mpr C.v'_mem_Q₁)

theorem Fv_comm_w₁' {f : X} (hf : f ∈ C.Fv) : f * C.w₁' = C.w₁' * f := by
  have hle : C.Fv ≤ centralizer ({C.w₁'} : Set X) := by
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]; exact (C.w₁'_comm_E0 he).symm
    · rw [mem_centralizer_singleton_iff]; exact C.w₁'_v'.symm
  exact mem_centralizer_singleton_iff.mp (hle hf)

theorem Fv_comm_w₂ {f : X} (hf : f ∈ C.Fv) : f * C.D₁.w₂ = C.D₁.w₂ * f := by
  have hle : C.Fv ≤ centralizer ({C.D₁.w₂} : Set X) := by
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]; exact (C.w₂_comm_E0 he).symm
    · rw [mem_centralizer_singleton_iff]; exact C.w₂_v'.symm
  exact mem_centralizer_singleton_iff.mp (hle hf)

theorem w₁'_w₂_ne : C.w₁' * C.D₁.w₂ ≠ C.D₁.w₂ * C.w₁' := fun h => C.ne_one_k (by
  rw [← C.comm_w₁'w₂, h]; group)

omit [Finite X] in
theorem comm_of_mul_comm {f g h : X} (hfh : f * h = h * f)
    (hx : f * g * h = h * (f * g)) : g * h = h * g := by
  have : f * (g * h) = f * (h * g) := by
    calc f * (g * h) = f * g * h := by group
      _ = h * (f * g) := hx
      _ = (h * f) * g := by group
      _ = (f * h) * g := by rw [hfh]
      _ = f * (h * g) := by group
  exact mul_left_cancel this

theorem mem_A₁_cases {x : X} (hx : x ∈ C.D₁.Q₁) (hxv : x * C.v' = C.v' * x)
    (hxw : x * C.w₁' = C.w₁' * x) : x ∈ C.Fv ∨ x * C.w₁'⁻¹ ∈ C.Fv := by
  rcases C.mem_B_cases hx hxv with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, x = f * C.D₁.w₂ := ⟨_, h, by group⟩
    exact C.w₁'_w₂_ne (comm_of_mul_comm (C.Fv_comm_w₁' hf) hxw).symm
  · exfalso
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, x = f * (C.w₁' * C.D₁.w₂) := ⟨_, h, by group⟩
    have h1 := comm_of_mul_comm (C.Fv_comm_w₁' hf) hxw
    rw [mul_assoc] at h1
    exact C.w₁'_w₂_ne (mul_left_cancel h1).symm

theorem mem_A₂_cases {x : X} (hx : x ∈ C.D₁.Q₁) (hxv : x * C.v' = C.v' * x)
    (hxw : x * C.D₁.w₂ = C.D₁.w₂ * x) : x ∈ C.Fv ∨ x * C.D₁.w₂⁻¹ ∈ C.Fv := by
  rcases C.mem_B_cases hx hxv with h | h | h | h
  · exact Or.inl h
  · exfalso
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, x = f * C.w₁' := ⟨_, h, by group⟩
    exact C.w₁'_w₂_ne (comm_of_mul_comm (C.Fv_comm_w₂ hf) hxw)
  · exact Or.inr h
  · exfalso
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, x = f * (C.w₁' * C.D₁.w₂) := ⟨_, h, by group⟩
    have h1 := comm_of_mul_comm (C.Fv_comm_w₂ hf) hxw
    rw [← mul_assoc] at h1
    exact C.w₁'_w₂_ne (mul_right_cancel h1)

theorem act_t_E₁ : act S.t C.E₁ = C.E₁ := by
  rw [C.E₁_eq]; exact C.act_Q₁ C.t_mem_Q₁ C.t_mem_Q₁

theorem sq_cases_q₁ {q : X} (hq : q ∈ C.S₂) (h0 : act q C.E₁ = C.G₁) (h1 : act q C.G₁ = C.E₁)
    (h2 : act q C.G₂ = C.G₃) (h3 : act q C.G₃ = C.G₂) :
    q ^ 2 ∈ C.D₁.Q₁ ∧ q ^ 2 * C.v' = C.v' * q ^ 2 ∧ (q ^ 2 ∈ C.Fv ∨ q ^ 2 * C.w₁'⁻¹ ∈ C.Fv) := by
  have hN := C.S₂_le hq
  have hE := C.conj_E0_q₁ hN h0 h1 h2
  obtain ⟨c0, -, c2⟩ := C.cong_q₁ hN h0 h1 h2
  have hsq : q ^ 2 ∈ C.D₁.Q₁ := C.sq_mem_Q₁_of hq (by rw [h0, h1]) (by rw [h2, h3])
  have hfix : C.Cong (q * q ^ 2 * q⁻¹) (q ^ 2) := by
    rw [show q * q ^ 2 * q⁻¹ = q ^ 2 by group]; exact C.cong_refl _
  have hv := C.comm_of_cong hN hE hsq hfix C.w₂_mem_Q₁ C.v'_mem_Q₁ c2
  have hc : C.Cong (q * S.t * q⁻¹) ((C.v' * C.w₁') * S.t) := by
    refine C.cong_trans c0 ?_
    rw [mul_assoc S.t]
    exact C.cong_comm C.t_mem_Q₁ (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁)
  have hvw := C.comm_of_cong hN hE hsq hfix C.t_mem_Q₁ (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁) hc
  have hw : q ^ 2 * C.w₁' = C.w₁' * q ^ 2 := by
    have : C.v' * (q ^ 2 * C.w₁') = C.v' * (C.w₁' * q ^ 2) := by
      rw [← mul_assoc, ← hv, mul_assoc, hvw, mul_assoc]
    exact mul_left_cancel this
  exact ⟨hsq, hv, C.mem_A₁_cases hsq hv hw⟩

theorem sq_cases_q₂ {q : X} (hq : q ∈ C.S₂) (h0 : act q C.E₁ = C.G₂) (h1 : act q C.G₁ = C.G₃)
    (h2 : act q C.G₂ = C.E₁) :
    q ^ 2 ∈ C.D₁.Q₁ ∧ q ^ 2 * C.v' = C.v' * q ^ 2 ∧
      (q ^ 2 ∈ C.Fv ∨ q ^ 2 * C.D₁.w₂⁻¹ ∈ C.Fv) := by
  have hN := C.S₂_le hq
  have hE := C.conj_E0_q₂ hN h0 h1 h2
  obtain ⟨c0, c1, -⟩ := C.cong_q₂ hN h0 h1 h2
  have hsq : q ^ 2 ∈ C.D₁.Q₁ := C.sq_mem_Q₁_of hq (by rw [h0, h2]) (by rw [h2, h0])
  have hfix : C.Cong (q * q ^ 2 * q⁻¹) (q ^ 2) := by
    rw [show q * q ^ 2 * q⁻¹ = q ^ 2 by group]; exact C.cong_refl _
  have hv := C.comm_of_cong hN hE hsq hfix C.w₁'_mem_Q₁ C.v'_mem_Q₁ c1
  have hc : C.Cong (q * S.t * q⁻¹) ((C.v' * C.D₁.w₂) * S.t) := by
    refine C.cong_trans c0 ?_
    rw [mul_assoc S.t]
    exact C.cong_comm C.t_mem_Q₁ (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁)
  have hvw := C.comm_of_cong hN hE hsq hfix C.t_mem_Q₁ (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁) hc
  have hw : q ^ 2 * C.D₁.w₂ = C.D₁.w₂ * q ^ 2 := by
    have : C.v' * (q ^ 2 * C.D₁.w₂) = C.v' * (C.D₁.w₂ * q ^ 2) := by
      rw [← mul_assoc, ← hv, mul_assoc, hvw, mul_assoc]
    exact mul_left_cancel this
  exact ⟨hsq, hv, C.mem_A₂_cases hsq hv hw⟩

theorem comm_v'_eq {q g : X} (hN : q ∈ normalizer (C.D₁.Q₁ : Set X))
    (hE : ∀ e ∈ C.E₀, q * e * q⁻¹ = e) (hc : C.Cong (q * g * q⁻¹) (C.v' * g)) :
    q ^ 2 * g * (q ^ 2)⁻¹ * g⁻¹ = q * C.v' * q⁻¹ * C.v'⁻¹ := by
  obtain ⟨f, hf, hfd⟩ : ∃ f ∈ C.E₀, q * g * q⁻¹ * g⁻¹ = f * C.v' :=
    ⟨q * g * q⁻¹ * g⁻¹ * C.v'⁻¹, by
      have := C.cong_def.mp hc
      rwa [show q * g * q⁻¹ * (C.v' * g)⁻¹ = q * g * q⁻¹ * g⁻¹ * C.v'⁻¹ by group] at this,
      by group⟩
  obtain ⟨c, hcE, hcv⟩ : ∃ c ∈ C.E₀, q * C.v' * q⁻¹ = c * C.v' :=
    ⟨q * C.v' * q⁻¹ * C.v'⁻¹, C.cong_def.mp (C.cong_v' hN), by group⟩
  have hel := C.isRefl_y.elemAbelianTwo_E0 C.isK_k
  have e1 : q ^ 2 * g * (q ^ 2)⁻¹ * g⁻¹ = q * (q * g * q⁻¹ * g⁻¹) * q⁻¹ *
      (q * g * q⁻¹ * g⁻¹) := by rw [pow_two]; group
  have e2 : q * (f * C.v') * q⁻¹ = f * (c * C.v') := by
    rw [conj_mul_eq, hE f hf, hcv]
  rw [e1, hfd, e2, show q * C.v' * q⁻¹ * C.v'⁻¹ = c by rw [hcv]; group]
  have hfv : C.v' * f = f * C.v' := C.comm_v'_E0 hf
  calc f * (c * C.v') * (f * C.v') = f * c * (C.v' * f) * C.v' := by group
    _ = f * c * (f * C.v') * C.v' := by rw [hfv]
    _ = (f * c * f) * (C.v' * C.v') := by group
    _ = c := by
        rw [C.v'v', mul_one, C.comm_E0 hf hcE, mul_assoc, ← pow_two, hel.sq_eq_one f hf,
          mul_one]

theorem exists_q₁' : ∃ q ∈ C.S₂, act q C.E₁ = C.G₁ ∧ act q C.G₁ = C.E₁ ∧
    act q C.G₂ = C.G₃ ∧ act q C.G₃ = C.G₂ ∧ q * C.v' = C.v' * q := by
  obtain ⟨q, hq, h0, h1, h2, h3⟩ := C.exists_q₁
  have hN := C.S₂_le hq
  have hE := C.conj_E0_q₁ hN h0 h1 h2
  obtain ⟨-, -, c2⟩ := C.cong_q₁ hN h0 h1 h2
  obtain ⟨hsq, -, hcases⟩ := C.sq_cases_q₁ hq h0 h1 h2 h3
  have hcv := C.comm_v'_eq hN hE c2
  have hc : q * C.v' * q⁻¹ * C.v'⁻¹ = 1 ∨ q * C.v' * q⁻¹ * C.v'⁻¹ = C.F.kF := by
    rw [← hcv]
    rcases hcases with h | h
    · left
      rw [C.Fv_comm_w₂ h]; group
    · right
      obtain ⟨f, hf, hfe⟩ : ∃ f ∈ C.Fv, q ^ 2 = f * C.w₁' := ⟨_, h, by group⟩
      rw [hfe, show f * C.w₁' * C.D₁.w₂ * (f * C.w₁')⁻¹ * C.D₁.w₂⁻¹ =
        f * (C.w₁' * C.D₁.w₂ * C.w₁'⁻¹ * C.D₁.w₂⁻¹) * (C.D₁.w₂ * f⁻¹ * C.D₁.w₂⁻¹) by group,
        C.comm_w₁'w₂, show C.D₁.w₂ * f⁻¹ * C.D₁.w₂⁻¹ = f⁻¹ by
          rw [← C.Fv_comm_w₂ (inv_mem hf)]; group]
      have hk : f * C.F.kF = C.F.kF * f := by
        have hF := (C.Fv_le_Q₁ hf)
        exact (C.comm_E0_Q₁ C.k_mem_E0 hF).symm
      rw [hk]; group
  rcases hc with hc | hc
  · refine ⟨q, hq, h0, h1, h2, h3, ?_⟩
    have : q * C.v' * q⁻¹ = C.v' := by
      calc q * C.v' * q⁻¹ = q * C.v' * q⁻¹ * C.v'⁻¹ * C.v' := by group
        _ = C.v' := by rw [hc, one_mul]
    calc q * C.v' = q * C.v' * q⁻¹ * q := by group
      _ = C.v' * q := by rw [this]
  · refine ⟨q * S.t, mul_mem hq (C.S₁_le_S₂ (C.Q₁_le_S₁ C.t_mem_Q₁)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [act_mul, C.act_t_E₁, h0]
    · rw [act_mul, C.act_Q₁ C.t_mem_Q₁ C.r₁_mem, h1]
    · rw [act_mul, C.act_Q₁ C.t_mem_Q₁ C.r₂_mem, h2]
    · rw [act_mul, C.act_Q₁ C.t_mem_Q₁ C.r₃_mem, h3]
    · have h1' : q * C.v' * q⁻¹ = C.F.kF * C.v' := by
        calc q * C.v' * q⁻¹ = q * C.v' * q⁻¹ * C.v'⁻¹ * C.v' := by group
          _ = C.F.kF * C.v' := by rw [hc]
      have : (q * S.t) * C.v' * (q * S.t)⁻¹ = C.v' := by
        rw [show (q * S.t) * C.v' * (q * S.t)⁻¹ = q * (S.t * C.v' * S.t⁻¹) * q⁻¹ by group,
          C.t_v', conj_mul_eq, hE _ C.k_mem_E0, h1', ← mul_assoc, C.kk, one_mul]
      calc q * S.t * C.v' = (q * S.t) * C.v' * (q * S.t)⁻¹ * (q * S.t) := by group
        _ = C.v' * (q * S.t) := by rw [this]

theorem exists_q₂' : ∃ q ∈ C.S₂, act q C.E₁ = C.G₂ ∧ act q C.G₂ = C.E₁ ∧
    act q C.G₁ = C.G₃ ∧ act q C.G₃ = C.G₁ ∧ q * C.v' = C.v' * q := by
  obtain ⟨q, hq, h0, h2, h1, h3⟩ := C.exists_q₂
  have hN := C.S₂_le hq
  have hE := C.conj_E0_q₂ hN h0 h1 h2
  obtain ⟨-, c1, -⟩ := C.cong_q₂ hN h0 h1 h2
  obtain ⟨hsq, -, hcases⟩ := C.sq_cases_q₂ hq h0 h1 h2
  have hcv := C.comm_v'_eq hN hE c1
  have hc : q * C.v' * q⁻¹ * C.v'⁻¹ = 1 ∨ q * C.v' * q⁻¹ * C.v'⁻¹ = C.F.kF := by
    rw [← hcv]
    rcases hcases with h | h
    · left
      rw [C.Fv_comm_w₁' h]; group
    · right
      obtain ⟨f, hf, hfe⟩ : ∃ f ∈ C.Fv, q ^ 2 = f * C.D₁.w₂ := ⟨_, h, by group⟩
      have hfw : f⁻¹ * C.w₁'⁻¹ = C.w₁'⁻¹ * f⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, C.Fv_comm_w₁' hf]
      rw [hfe, show f * C.D₁.w₂ * C.w₁' * (f * C.D₁.w₂)⁻¹ * C.w₁'⁻¹ =
        f * (C.D₁.w₂ * C.w₁' * C.D₁.w₂⁻¹) * (f⁻¹ * C.w₁'⁻¹) by group, C.w₂_w₁', hfw]
      have hk : f * C.F.kF = C.F.kF * f := (C.comm_E0_Q₁ C.k_mem_E0 (C.Fv_le_Q₁ hf)).symm
      rw [show f * (C.F.kF * C.w₁') * (C.w₁'⁻¹ * f⁻¹) = f * C.F.kF * f⁻¹ by group, hk]
      group
  rcases hc with hc | hc
  · refine ⟨q, hq, h0, h2, h1, h3, ?_⟩
    have : q * C.v' * q⁻¹ = C.v' := by
      calc q * C.v' * q⁻¹ = q * C.v' * q⁻¹ * C.v'⁻¹ * C.v' := by group
        _ = C.v' := by rw [hc, one_mul]
    calc q * C.v' = q * C.v' * q⁻¹ * q := by group
      _ = C.v' * q := by rw [this]
  · refine ⟨q * S.t, mul_mem hq (C.S₁_le_S₂ (C.Q₁_le_S₁ C.t_mem_Q₁)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [act_mul, C.act_t_E₁, h0]
    · rw [act_mul, C.act_Q₁ C.t_mem_Q₁ C.r₂_mem, h2]
    · rw [act_mul, C.act_Q₁ C.t_mem_Q₁ C.r₁_mem, h1]
    · rw [act_mul, C.act_Q₁ C.t_mem_Q₁ C.r₃_mem, h3]
    · have h1' : q * C.v' * q⁻¹ = C.F.kF * C.v' := by
        calc q * C.v' * q⁻¹ = q * C.v' * q⁻¹ * C.v'⁻¹ * C.v' := by group
          _ = C.F.kF * C.v' := by rw [hc]
      have : (q * S.t) * C.v' * (q * S.t)⁻¹ = C.v' := by
        rw [show (q * S.t) * C.v' * (q * S.t)⁻¹ = q * (S.t * C.v' * S.t⁻¹) * q⁻¹ by group,
          C.t_v', conj_mul_eq, hE _ C.k_mem_E0, h1', ← mul_assoc, C.kk, one_mul]
      calc q * S.t * C.v' = (q * S.t) * C.v' * (q * S.t)⁻¹ * (q * S.t) := by group
        _ = C.v' * (q * S.t) := by rw [this]

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
