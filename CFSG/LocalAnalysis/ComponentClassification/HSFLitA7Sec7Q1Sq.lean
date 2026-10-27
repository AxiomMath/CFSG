module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Q1

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem conj_eq_of_mem_Q₁ {g e : X} (hg : g ∈ C.D₁.Q₁) (he : e ∈ C.E₀) : g * e * g⁻¹ = e := by
  rw [C.Q₁_eq] at hg
  exact (C.mem_Tm.mp (C.Q₁'_le_Tm hg)).1 e he

theorem comm_E0_Q₁ {e g : X} (he : e ∈ C.E₀) (hg : g ∈ C.D₁.Q₁) : e * g = g * e := by
  have := C.conj_eq_of_mem_Q₁ hg he
  calc e * g = g * e * g⁻¹ * g := by rw [this]
    _ = g * e := by group

theorem E0_le_Q₁ : C.E₀ ≤ C.D₁.Q₁ := by rw [C.Q₁_eq]; exact C.E0_le_Q₁'

theorem E₁_le_Q₁ : C.E₁ ≤ C.D₁.Q₁ := by
  rw [C.Q₁_eq]; exact le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem t_mem_Q₁ : S.t ∈ C.D₁.Q₁ := C.E₁_le_Q₁ C.t_mem_E₁

theorem v'_mem_Q₁ : C.v' ∈ C.D₁.Q₁ := by
  rw [C.Q₁_eq]; exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem w₁'_mem_Q₁ : C.w₁' ∈ C.D₁.Q₁ := by
  rw [C.Q₁_eq]; exact mem_sup_left (mem_sup_right (mem_zpowers _))

theorem w₂_mem_Q₁ : C.D₁.w₂ ∈ C.D₁.Q₁ := by
  rw [C.Q₁_eq]; exact mem_sup_right (mem_zpowers _)

theorem tmov_mul {p q : X} (hp : p ∈ C.Tm C.E₀ le_rfl) (hq : q ∈ C.Tm C.E₀ le_rfl) :
    S.t⁻¹ * (p * q * S.t * (p * q)⁻¹) =
      (S.t⁻¹ * (p * S.t * p⁻¹)) * (S.t⁻¹ * (q * S.t * q⁻¹)) := by
  have h1 : p * q * S.t * (p * q)⁻¹ = (p * S.t * p⁻¹) *
      (p * (S.t⁻¹ * (q * S.t * q⁻¹)) * p⁻¹) := by group
  rw [h1, (C.mem_Tm.mp hp).1 _ (C.mem_Tm.mp hq).2]
  group

theorem mem_E₁_of_comm_t {x : X} (hx : x ∈ C.D₁.Q₁) (hxt : x * S.t = S.t * x) : x ∈ C.E₁ := by
  rw [C.Q₁_eq] at hx
  have hfix : S.t⁻¹ * (x * S.t * x⁻¹) = 1 := by rw [hxt, mul_inv_cancel_right, inv_mul_cancel]
  have hTm : ∀ {a b : X}, a ∈ C.Q₁' → b ∈ C.Q₁' →
      S.t⁻¹ * (a * b * S.t * (a * b)⁻¹) = (S.t⁻¹ * (a * S.t * a⁻¹)) * (S.t⁻¹ * (b * S.t * b⁻¹)) :=
    fun ha hb => C.tmov_mul (C.Q₁'_le_Tm ha) (C.Q₁'_le_Tm hb)
  have hx3 : x ∈ C.P₃ := by
    rcases mem_or_of_mem_sup_zpowers C.w₂_normalizes_P₃ (C.E0_le_P₃ C.w₂_sq_mem) hx with h | h
    · exact h
    · exfalso
      have hp := (C.mem_Tm.mp (C.P₃_le_Tm h)).2
      have := hTm (mem_sup_left h) (mem_sup_right (mem_zpowers C.D₁.w₂))
      rw [show x * C.D₁.w₂⁻¹ * C.D₁.w₂ = x by group, hfix, C.w₂_t, inv_mul_cancel_left] at this
      apply C.isRefl_y.not_mem_B
      have hy : C.F.yF = (S.t⁻¹ * (x * C.D₁.w₂⁻¹ * S.t * (x * C.D₁.w₂⁻¹)⁻¹))⁻¹ :=
        eq_inv_of_mul_eq_one_right this.symm
      rw [hy]
      exact inv_mem (zk_le_B C.isK_k hp)
  have hx2 : x ∈ C.P₂ := by
    rcases mem_or_of_mem_sup_zpowers C.w₁'_normalizes_P₂ (C.E0_le_P₂ C.w₁'_sq_mem_E0) hx3 with
      h | h
    · exact h
    · exfalso
      have hp := (C.mem_Tm.mp (C.P₂_le_Tm h)).2
      have := hTm (mem_sup_left (mem_sup_left h)) (mem_sup_left (mem_sup_right
        (mem_zpowers C.w₁')))
      rw [show x * C.w₁'⁻¹ * C.w₁' = x by group, hfix, C.w₁'_t, inv_mul_cancel_left] at this
      apply C.k_not_mem_zpowers_z
      have hz : S.z = (S.t⁻¹ * (x * C.w₁'⁻¹ * S.t * (x * C.w₁'⁻¹)⁻¹))⁻¹ :=
        eq_inv_of_mul_eq_one_right this.symm
      rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq hp with h1 | h1
      · rw [h1, inv_one] at hz; exact absurd hz S.z_ne_one
      · rw [h1, inv_eq_of_mul_eq_one_right C.kk] at hz; rw [← hz]; exact mem_zpowers _
  rcases mem_or_of_mem_sup_zpowers C.v'_normalizes_E₁ C.v'_sq_mem hx2 with h | h
  · exact h
  · exfalso
    have hp := (C.mem_Tm.mp (C.E₁_le_Tm ⊥ bot_le h)).2
    rw [mem_bot] at hp
    have := hTm (mem_sup_left (mem_sup_left (mem_sup_left h)))
      (mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers C.v'))))
    rw [show x * C.v'⁻¹ * C.v' = x by group, hfix, C.v'_t, inv_mul_cancel_left, hp, one_mul]
      at this
    exact C.isK_k.ne_one this.symm

theorem mem_E0_of_comm_v' {x : X} (hx : x ∈ C.E₁) (hxv : x * C.v' = C.v' * x) : x ∈ C.E₀ := by
  rcases C.isRefl_y.mem_E0_or C.isK_k hx with h | h
  · exact h
  · exfalso
    have hxe : x = (x * S.t) * S.t := by rw [mul_assoc, tt S, mul_one]
    have hev := C.comm_v'_E0 h
    have htv : S.t * C.v' = C.v' * S.t := by
      have h1 : (x * S.t) * (S.t * C.v') = (x * S.t) * (C.v' * S.t) := by
        calc (x * S.t) * (S.t * C.v') = x * C.v' := by rw [mul_assoc, ← mul_assoc S.t, tt S,
              one_mul]
          _ = C.v' * x := hxv
          _ = C.v' * (x * S.t) * S.t := by rw [mul_assoc C.v', mul_assoc, tt S, mul_one]
          _ = (x * S.t) * (C.v' * S.t) := by rw [hev, mul_assoc]
      exact mul_left_cancel h1
    have := C.v'_t
    rw [← htv, mul_inv_cancel_right] at this
    exact C.isK_k.ne_one (by simpa using this.symm)

theorem mem_E0_of_mem_center {x : X} (hx : x ∈ C.D₁.Q₁) (hc : ∀ g ∈ C.D₁.Q₁, x * g = g * x) :
    x ∈ C.E₀ :=
  C.mem_E0_of_comm_v' (C.mem_E₁_of_comm_t hx (hc _ C.t_mem_Q₁)) (hc _ C.v'_mem_Q₁)

theorem conj_E0_of_mem_normalizer {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) {e : X}
    (he : e ∈ C.E₀) : n * e * n⁻¹ ∈ C.E₀ := by
  have heQ := C.E0_le_Q₁ he
  refine C.mem_E0_of_mem_center ((mem_normalizer_iff.mp hn e).mp heQ) fun g hg => ?_
  have hg' : n⁻¹ * g * n ∈ C.D₁.Q₁ := by
    have := (mem_normalizer_iff.mp (inv_mem hn) g).mp hg
    rwa [inv_inv] at this
  have h1 := C.comm_E0_Q₁ he hg'
  calc n * e * n⁻¹ * g = n * (e * (n⁻¹ * g * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * g * n) * e) * n⁻¹ := by rw [h1]
    _ = g * (n * e * n⁻¹) := by group

theorem case_data :
    (C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ = S.z ∧ C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * C.v'⁻¹ = C.F.yF ∧
      C.w₁' ^ 2 = C.F.kF ∧ C.D₁.w₂ ^ 2 = C.F.kF) ∨
    (C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ = 1 ∧ C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * C.v'⁻¹ = 1 ∧
      C.w₁' ^ 2 = S.z * C.F.kF ∧ C.D₁.w₂ ^ 2 = C.F.yF * C.F.kF) := by
  have h := C.D₁.q0_holds
  rcases C.w₂_v'_cases with ⟨hq, h2⟩ | ⟨hq, h2⟩ <;> rw [hq] at h
  · left
    exact ⟨C.comm_w₁'_v'_e4q8 hq, by rw [h2, mul_inv_cancel_right], by rw [C.w₁'_sq]; exact h.1,
      h.2.1⟩
  · right
    exact ⟨C.comm_w₁'_v'_exc hq, by rw [h2, mul_inv_cancel], by rw [C.w₁'_sq]; exact h.1, h.2.1⟩

theorem ne_one_k : C.F.kF ≠ 1 := C.isK_k.ne_one

theorem ne_one_zk : S.z * C.F.kF ≠ 1 := (isK_zkF C.F).ne_one

theorem ne_one_yk : C.F.yF * C.F.kF ≠ 1 := by
  intro h
  apply C.isRefl_y.not_mem_B
  rw [eq_inv_of_mul_eq_one_left h]
  exact inv_mem (kF_mem_B C.F)

theorem ne_one_zyk : S.z * C.F.yF * C.F.kF ≠ 1 := by
  intro h
  apply C.isRefl_y.not_mem_B
  have : C.F.yF = S.z⁻¹ * C.F.kF⁻¹ := by
    rw [show S.z⁻¹ * C.F.kF⁻¹ = S.z⁻¹ * (S.z * C.F.yF * C.F.kF) * C.F.kF⁻¹ by rw [h]; group]
    group
  rw [this]
  exact mul_mem (inv_mem z_mem_B) (inv_mem (kF_mem_B C.F))

theorem kz : C.F.kF * S.z = S.z * C.F.kF := commute_of_mem_B (kF_mem_B C.F) z_mem_B

theorem yz : C.F.yF * S.z = S.z * C.F.yF := C.comm_E0 C.y_mem_E0 C.z_mem_E0

theorem ky : C.F.kF * C.F.yF = C.F.yF * C.F.kF := C.comm_E0 C.k_mem_E0 C.y_mem_E0

theorem sq_v'_mul {m : X} (hc : m * C.v' * m⁻¹ * C.v'⁻¹ ∈ C.E₀) :
    (C.v' * m) ^ 2 = (m * C.v' * m⁻¹ * C.v'⁻¹) * m ^ 2 := by
  rw [sq_mul_eq (C.comm_v'_E0 hc), C.v'_sq, mul_one]

theorem sq_t_mul {m : X} (hm : m ∈ C.D₁.Q₁) :
    (S.t * m) ^ 2 = (m * S.t * m⁻¹ * S.t⁻¹) * m ^ 2 := by
  have hc : m * S.t * m⁻¹ * S.t⁻¹ ∈ C.E₀ := by
    rw [C.Q₁_eq] at hm
    have h1 := (C.mem_Tm.mp (C.Q₁'_le_Tm hm)).2
    rw [show m * S.t * m⁻¹ * S.t⁻¹ = S.t * (S.t⁻¹ * (m * S.t * m⁻¹)) * S.t⁻¹ by group]
    rw [conj_eq_of_comm (C.t_comm_E0 h1)]
    exact h1
  rw [sq_mul_eq (C.t_comm_E0 hc), S.t_sq, mul_one]

theorem sq_w₁'_ne : C.w₁' ^ 2 ≠ 1 := by
  rcases C.case_data with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> rw [h]
  · exact C.ne_one_k
  · exact C.ne_one_zk

theorem sq_w₂_ne : C.D₁.w₂ ^ 2 ≠ 1 := by
  rcases C.case_data with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact C.ne_one_k
  · exact C.ne_one_yk

theorem sq_v'w₁' : (C.v' * C.w₁') ^ 2 = S.z * C.F.kF := by
  rw [C.sq_v'_mul C.c₁_mem]
  rcases C.case_data with ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩ <;> rw [h1, h3]
  rw [one_mul]

theorem sq_v'w₂ : (C.v' * C.D₁.w₂) ^ 2 = C.F.yF * C.F.kF := by
  rw [C.sq_v'_mul C.c₂_mem]
  rcases C.case_data with ⟨-, h2, -, h4⟩ | ⟨-, h2, -, h4⟩ <;> rw [h2, h4]
  rw [one_mul]

theorem sq_w₁'w₂ : (C.w₁' * C.D₁.w₂) ^ 2 = C.F.kF * C.w₁' ^ 2 * C.D₁.w₂ ^ 2 := by
  have hk : C.D₁.w₂ * C.w₁' * C.D₁.w₂⁻¹ * C.w₁'⁻¹ = C.F.kF := by
    rw [C.w₂_w₁', mul_inv_cancel_right]
  rw [sq_mul_eq (by rw [hk]; exact (C.w₁'_comm_E0 C.k_mem_E0)), hk]

theorem sq_w₁'w₂_ne : (C.w₁' * C.D₁.w₂) ^ 2 ≠ 1 := by
  rw [C.sq_w₁'w₂]
  rcases C.case_data with ⟨-, -, h3, h4⟩ | ⟨-, -, h3, h4⟩ <;> rw [h3, h4]
  · rw [mul_assoc, C.kk, mul_one]; exact C.ne_one_k
  · rw [← mul_assoc C.F.kF, C.kz, mul_assoc S.z, C.kk, mul_one, ← mul_assoc]
    exact C.ne_one_zyk

theorem comm_t_val {m a : X} (h : m * S.t * m⁻¹ = S.t * a) (ha : a ∈ C.E₀) :
    m * S.t * m⁻¹ * S.t⁻¹ = a := by
  rw [h, conj_eq_of_comm (C.t_comm_E0 ha)]

theorem w₁'w₂_t : (C.w₁' * C.D₁.w₂) * S.t * (C.w₁' * C.D₁.w₂)⁻¹ = S.t * (S.z * C.F.yF) := by
  rw [show C.w₁' * C.D₁.w₂ * S.t * (C.w₁' * C.D₁.w₂)⁻¹ =
    C.w₁' * (C.D₁.w₂ * S.t * C.D₁.w₂⁻¹) * C.w₁'⁻¹ by group, C.w₂_t, conj_mul_eq, C.w₁'_t,
    C.w₁'_E0 C.y_mem_E0, mul_assoc]

theorem comm_w₁'w₂_v' : (C.w₁' * C.D₁.w₂) * C.v' * (C.w₁' * C.D₁.w₂)⁻¹ * C.v'⁻¹ =
    (C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * C.v'⁻¹) * (C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹) := by
  have hc₂ := C.c₂_mem
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂'⟩ : ∃ c, c = C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * C.v'⁻¹ := ⟨_, rfl⟩
  rw [← hc₂'] at hc₂
  rw [← hc₁, ← hc₂']
  have h2 : C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ = c₂ * C.v' := by rw [hc₂']; group
  have h1 : C.w₁' * C.v' * C.w₁'⁻¹ = c₁ * C.v' := by rw [hc₁]; group
  calc C.w₁' * C.D₁.w₂ * C.v' * (C.w₁' * C.D₁.w₂)⁻¹ * C.v'⁻¹ =
        C.w₁' * (C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹) * C.w₁'⁻¹ * C.v'⁻¹ := by group
    _ = (C.w₁' * c₂ * C.w₁'⁻¹) * (C.w₁' * C.v' * C.w₁'⁻¹) * C.v'⁻¹ := by rw [h2]; group
    _ = c₂ * c₁ := by rw [C.w₁'_E0 hc₂, h1]; group

theorem sq_v'w₁'w₂ : (C.v' * C.w₁' * C.D₁.w₂) ^ 2 = S.z * C.F.yF * C.F.kF := by
  have hc : (C.w₁' * C.D₁.w₂) * C.v' * (C.w₁' * C.D₁.w₂)⁻¹ * C.v'⁻¹ ∈ C.E₀ := by
    rw [C.comm_w₁'w₂_v']; exact mul_mem C.c₂_mem C.c₁_mem
  rw [mul_assoc, C.sq_v'_mul hc, C.comm_w₁'w₂_v', C.sq_w₁'w₂]
  rcases C.case_data with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> rw [h1, h2, h3, h4]
  · rw [mul_assoc C.F.kF, C.kk, mul_one, C.yz]
  · rw [one_mul, one_mul, ← mul_assoc C.F.kF, C.kz, mul_assoc S.z, C.kk, mul_one, ← mul_assoc]

theorem sq_tv' : (S.t * C.v') ^ 2 = C.F.kF := by
  rw [C.sq_t_mul C.v'_mem_Q₁, C.comm_t_val C.v'_t C.k_mem_E0, C.v'_sq, mul_one]

theorem sq_tw₁'_ne : (S.t * C.w₁') ^ 2 ≠ 1 := by
  rw [C.sq_t_mul C.w₁'_mem_Q₁, C.comm_t_val C.w₁'_t C.z_mem_E0]
  rcases C.case_data with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ <;> rw [h3]
  · exact C.ne_one_zk
  · rw [← mul_assoc, zz S, one_mul]; exact C.ne_one_k

theorem sq_tw₂_ne : (S.t * C.D₁.w₂) ^ 2 ≠ 1 := by
  rw [C.sq_t_mul C.w₂_mem_Q₁, C.comm_t_val C.w₂_t C.y_mem_E0]
  rcases C.case_data with ⟨-, -, -, h4⟩ | ⟨-, -, -, h4⟩ <;> rw [h4]
  · exact C.ne_one_yk
  · rw [← mul_assoc, C.yy, one_mul]; exact C.ne_one_k

theorem sq_tw₁'w₂_ne : (S.t * C.w₁' * C.D₁.w₂) ^ 2 ≠ 1 := by
  rw [mul_assoc, C.sq_t_mul (mul_mem C.w₁'_mem_Q₁ C.w₂_mem_Q₁),
    C.comm_t_val C.w₁'w₂_t (mul_mem C.z_mem_E0 C.y_mem_E0), C.sq_w₁'w₂]
  rcases C.case_data with ⟨-, -, h3, h4⟩ | ⟨-, -, h3, h4⟩ <;> rw [h3, h4]
  · rw [mul_assoc C.F.kF, C.kk, mul_one]; exact C.ne_one_zyk
  ·
    have e1 : C.F.kF * (S.z * C.F.kF) * (C.F.yF * C.F.kF) = S.z * C.F.yF * C.F.kF := by
      rw [← mul_assoc C.F.kF, C.kz, mul_assoc S.z, C.kk, mul_one, ← mul_assoc]
    have e2 : S.z * C.F.yF * (S.z * C.F.yF) = 1 := by
      rw [← pow_two]
      exact (C.isRefl_y.elemAbelianTwo_E0 C.isK_k).sq_eq_one _ (mul_mem C.z_mem_E0 C.y_mem_E0)
    have : S.z * C.F.yF * (C.F.kF * (S.z * C.F.kF) * (C.F.yF * C.F.kF)) = C.F.kF := by
      rw [e1, ← mul_assoc, e2, one_mul]
    rw [this]; exact C.ne_one_k

theorem sq_of_coset {x n : X} (hn : n ∈ C.D₁.Q₁) (h : x * n⁻¹ ∈ C.E₀) : x ^ 2 = n ^ 2 := by
  obtain ⟨e, he, rfl⟩ : ∃ e ∈ C.E₀, x = e * n := ⟨x * n⁻¹, h, by group⟩
  rw [pow_two, pow_two, show e * n * (e * n) = e * (n * e) * n by group,
    ← C.comm_E0_Q₁ he hn, show e * (e * n) * n = (e * e) * (n * n) by group, ← pow_two e,
    (C.isRefl_y.elemAbelianTwo_E0 C.isK_k).sq_eq_one e he, one_mul]

theorem inv_cases {x : X} (hx : x ∈ C.D₁.Q₁) (hx2 : x ^ 2 = 1) :
    x ∈ C.E₀ ∨ x * S.t⁻¹ ∈ C.E₀ ∨ x * C.v'⁻¹ ∈ C.E₀ ∨ x * (S.t * C.v' * C.w₁')⁻¹ ∈ C.E₀ ∨
      x * (S.t * C.v' * C.D₁.w₂)⁻¹ ∈ C.E₀ ∨
      x * (S.t * C.v' * C.w₁' * C.D₁.w₂)⁻¹ ∈ C.E₀ := by
  have hQ := hx
  rw [C.Q₁_eq] at hx
  have ht := C.t_mem_Q₁
  have hv := C.v'_mem_Q₁
  have hw₁ := C.w₁'_mem_Q₁
  have hw₂ := C.w₂_mem_Q₁
  have hti : S.t⁻¹ = S.t := t_inv S
  have bad : ∀ n ∈ C.D₁.Q₁, n ^ 2 ≠ 1 → ∀ y, y ∈ C.E₀ → y = x * n⁻¹ → False :=
    fun n hn hn2 y hy hyx => hn2 (by rw [← C.sq_of_coset hn (hyx ▸ hy), hx2])
  have s3 : ∀ {a : X}, a ∈ C.Q₁' → a ∈ C.P₃ ∨ a * C.D₁.w₂⁻¹ ∈ C.P₃ := fun ha =>
    mem_or_of_mem_sup_zpowers C.w₂_normalizes_P₃ (C.E0_le_P₃ C.w₂_sq_mem) ha
  have s2 : ∀ {a : X}, a ∈ C.P₃ → a ∈ C.P₂ ∨ a * C.w₁'⁻¹ ∈ C.P₂ := fun ha =>
    mem_or_of_mem_sup_zpowers C.w₁'_normalizes_P₂ (C.E0_le_P₂ C.w₁'_sq_mem_E0) ha
  have s1 : ∀ {a : X}, a ∈ C.P₂ → a ∈ C.E₁ ∨ a * C.v'⁻¹ ∈ C.E₁ := fun ha =>
    mem_or_of_mem_sup_zpowers C.v'_normalizes_E₁ C.v'_sq_mem ha
  have s0 : ∀ {y : X}, y ∈ C.E₁ → y ∈ C.E₀ ∨ y * S.t ∈ C.E₀ :=
    fun hy => C.isRefl_y.mem_E0_or C.isK_k hy
  rcases s3 hx with h3 | h3
  · rcases s2 h3 with h2 | h2
    · rcases s1 h2 with h1 | h1
      · rcases s0 h1 with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Or.inl (by rw [hti]; exact h0))
      · rcases s0 h1 with h0 | h0
        · exact Or.inr (Or.inr (Or.inl h0))
        · exact (bad _ (mul_mem ht hv) (by rw [C.sq_tv']; exact C.ne_one_k) _ h0
            (by simp only [mul_inv_rev, hti]; group)).elim
    · rcases s1 h2 with h1 | h1
      · rcases s0 h1 with h0 | h0
        · exact (bad _ hw₁ C.sq_w₁'_ne _ h0 (by group)).elim
        · exact (bad _ (mul_mem ht hw₁) C.sq_tw₁'_ne _ h0
            (by simp only [mul_inv_rev, hti]; group)).elim
      · rcases s0 h1 with h0 | h0
        · exact (bad _ (mul_mem hv hw₁) (by rw [C.sq_v'w₁']; exact C.ne_one_zk) _ h0
            (by group)).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
            rw [show x * (S.t * C.v' * C.w₁')⁻¹ = x * C.w₁'⁻¹ * C.v'⁻¹ * S.t by
              simp only [mul_inv_rev, hti]; group]
            exact h0))))
  · rcases s2 h3 with h2 | h2
    · rcases s1 h2 with h1 | h1
      · rcases s0 h1 with h0 | h0
        · exact (bad _ hw₂ C.sq_w₂_ne _ h0 (by group)).elim
        · exact (bad _ (mul_mem ht hw₂) C.sq_tw₂_ne _ h0
            (by simp only [mul_inv_rev, hti]; group)).elim
      · rcases s0 h1 with h0 | h0
        · exact (bad _ (mul_mem hv hw₂) (by rw [C.sq_v'w₂]; exact C.ne_one_yk) _ h0
            (by group)).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
            rw [show x * (S.t * C.v' * C.D₁.w₂)⁻¹ = x * C.D₁.w₂⁻¹ * C.v'⁻¹ * S.t by
              simp only [mul_inv_rev, hti]; group]
            exact h0)))))
    · rcases s1 h2 with h1 | h1
      · rcases s0 h1 with h0 | h0
        · exact (bad _ (mul_mem hw₁ hw₂) C.sq_w₁'w₂_ne _ h0 (by group)).elim
        · exact (bad _ (mul_mem (mul_mem ht hw₁) hw₂) C.sq_tw₁'w₂_ne _ h0
            (by simp only [mul_inv_rev, hti]; group)).elim
      · rcases s0 h1 with h0 | h0
        · exact (bad _ (mul_mem (mul_mem hv hw₁) hw₂)
            (by rw [C.sq_v'w₁'w₂]; exact C.ne_one_zyk) _ h0 (by group)).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
            rw [show x * (S.t * C.v' * C.w₁' * C.D₁.w₂)⁻¹ =
              x * C.D₁.w₂⁻¹ * C.w₁'⁻¹ * C.v'⁻¹ * S.t by
              simp only [mul_inv_rev, hti]; group]
            exact h0)))))

abbrev Fv : Subgroup X := C.E₀ ⊔ zpowers C.v'

abbrev G₁ : Subgroup X := C.E₀ ⊔ zpowers (S.t * C.v' * C.w₁')

abbrev G₂ : Subgroup X := C.E₀ ⊔ zpowers (S.t * C.v' * C.D₁.w₂)

abbrev G₃ : Subgroup X := C.E₀ ⊔ zpowers (S.t * C.v' * C.w₁' * C.D₁.w₂)

theorem sup_zpowers_eq_of_coset {x r : X} (h : x * r⁻¹ ∈ C.E₀) :
    C.E₀ ⊔ zpowers x = C.E₀ ⊔ zpowers r := by
  apply le_antisymm
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    rw [show x = x * r⁻¹ * r by group]
    exact mul_mem (mem_sup_left h) (mem_sup_right (mem_zpowers _))
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    rw [show r = (x * r⁻¹)⁻¹ * x by group]
    exact mul_mem (mem_sup_left (inv_mem h)) (mem_sup_right (mem_zpowers _))

theorem map_E0_of_mem_normalizer {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) :
    C.E₀.map (MulAut.conj n).toMonoidHom = C.E₀ := by
  have hle : C.E₀.map (MulAut.conj n).toMonoidHom ≤ C.E₀ := by
    rintro _ ⟨e, he, rfl⟩
    exact C.conj_E0_of_mem_normalizer hn he
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj n).injective])

theorem conj_E₁_cases {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) :
    C.E₁.map (MulAut.conj n).toMonoidHom = C.E₁ ∨ C.E₁.map (MulAut.conj n).toMonoidHom = C.Fv ∨
      C.E₁.map (MulAut.conj n).toMonoidHom = C.G₁ ∨
      C.E₁.map (MulAut.conj n).toMonoidHom = C.G₂ ∨
      C.E₁.map (MulAut.conj n).toMonoidHom = C.G₃ := by
  have hmap : C.E₁.map (MulAut.conj n).toMonoidHom = C.E₀ ⊔ zpowers (n * S.t * n⁻¹) := by
    rw [C.E₁_eq, Subgroup.map_sup, C.map_E0_of_mem_normalizer hn, MonoidHom.map_zpowers]
    rfl
  have hxQ : n * S.t * n⁻¹ ∈ C.D₁.Q₁ := (mem_normalizer_iff.mp hn _).mp C.t_mem_Q₁
  have hx2 : (n * S.t * n⁻¹) ^ 2 = 1 := by
    rw [show (n * S.t * n⁻¹) ^ 2 = n * S.t ^ 2 * n⁻¹ by rw [pow_two, pow_two]; group, S.t_sq]
    group
  have hxE : n * S.t * n⁻¹ ∉ C.E₀ := by
    intro h
    apply C.isRefl_y.t_not_mem_E0 C.isK_k
    have := C.conj_E0_of_mem_normalizer (inv_mem hn) h
    rwa [show n⁻¹ * (n * S.t * n⁻¹) * n⁻¹⁻¹ = S.t by group] at this
  rw [hmap]
  rcases C.inv_cases hxQ hx2 with h | h | h | h | h | h
  · exact absurd h hxE
  · left; rw [C.sup_zpowers_eq_of_coset h, C.E₁_eq]
  · right; left; rw [C.sup_zpowers_eq_of_coset h]
  · right; right; left; rw [C.sup_zpowers_eq_of_coset h]
  · right; right; right; left; rw [C.sup_zpowers_eq_of_coset h]
  · right; right; right; right; rw [C.sup_zpowers_eq_of_coset h]

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
