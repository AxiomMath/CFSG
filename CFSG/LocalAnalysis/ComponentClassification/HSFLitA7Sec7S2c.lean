module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2b

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem exc : C.D₁.q0 = .exceptional :=
  C.hq.resolve_left fun h => C.false_of_e4q8 h

theorem alpha_eq_one_iff {x : X} : alpha S x = 1 ↔ x * S.t = S.t * x := by
  rw [alpha_def]
  constructor
  · intro h
    have h1 : x * S.t * x⁻¹ = S.t := by
      calc x * S.t * x⁻¹ = S.t * (S.t⁻¹ * (x * S.t * x⁻¹)) := by group
        _ = S.t := by rw [h, mul_one]
    calc x * S.t = x * S.t * x⁻¹ * x := by group
      _ = S.t * x := by rw [h1]
  · intro h
    rw [h]; group

def beta (x : X) : X := C.v'⁻¹ * (x * C.v' * x⁻¹)

theorem beta_def (x : X) : C.beta x = C.v'⁻¹ * (x * C.v' * x⁻¹) := by unfold beta; rfl

theorem beta_mul {x y : X} (hx : x ∈ C.D₁.Q₁) (hy : y ∈ C.D₁.Q₁) :
    C.beta (x * y) = C.beta x * C.beta y := by
  rw [C.beta_def, C.beta_def, C.beta_def]
  exact C.tma_mul (C.Q₁_le_Tma_v' hx) (C.Q₁_le_Tma_v' hy)

theorem beta_inv {x : X} (hx : x ∈ C.D₁.Q₁) : C.beta x⁻¹ = (C.beta x)⁻¹ := by
  rw [C.beta_def, C.beta_def]
  exact C.tma_inv (C.Q₁_le_Tma_v' hx)

theorem beta_of_mem_E0 {e : X} (he : e ∈ C.E₀) : C.beta e = 1 := by
  rw [C.beta_def, conj_eq_of_comm (C.comm_v'_E0 he).symm, inv_mul_cancel]

theorem beta_eq_one_iff {x : X} : C.beta x = 1 ↔ x * C.v' = C.v' * x := by
  rw [C.beta_def]
  constructor
  · intro h
    have h1 : x * C.v' * x⁻¹ = C.v' := by
      calc x * C.v' * x⁻¹ = C.v' * (C.v'⁻¹ * (x * C.v' * x⁻¹)) := by group
        _ = C.v' := by rw [h, mul_one]
    calc x * C.v' = x * C.v' * x⁻¹ * x := by group
      _ = C.v' * x := by rw [h1]
  · intro h
    rw [h]; group

theorem beta_t : C.beta S.t = C.F.kF := by
  rw [C.beta_def, C.t_v', ← C.comm_v'_E0 C.k_mem_E0, inv_mul_cancel_left]

theorem beta_v' : C.beta C.v' = 1 := by rw [C.beta_def]; group

theorem w₁'_v' : C.w₁' * C.v' = C.v' * C.w₁' := by
  have h := C.comm_w₁'_v'_exc C.exc
  calc C.w₁' * C.v' = C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ * (C.v' * C.w₁') := by group
    _ = C.v' * C.w₁' := by rw [h, one_mul]

theorem w₂_v' : C.D₁.w₂ * C.v' = C.v' * C.D₁.w₂ := (C.v'_comm_Q0 C.exc C.w₂_mem_Q0).symm

theorem beta_w₁' : C.beta C.w₁' = 1 := C.beta_eq_one_iff.mpr C.w₁'_v'

theorem beta_w₂ : C.beta C.D₁.w₂ = 1 := C.beta_eq_one_iff.mpr C.w₂_v'

theorem beta_r₁ : C.beta (S.t * C.v' * C.w₁') = C.F.kF := by
  rw [C.beta_mul (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₁'_mem_Q₁,
    C.beta_mul C.t_mem_Q₁ C.v'_mem_Q₁, C.beta_t, C.beta_v', C.beta_w₁', mul_one, mul_one]

theorem beta_r₂ : C.beta (S.t * C.v' * C.D₁.w₂) = C.F.kF := by
  rw [C.beta_mul (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₂_mem_Q₁,
    C.beta_mul C.t_mem_Q₁ C.v'_mem_Q₁, C.beta_t, C.beta_v', C.beta_w₂, mul_one, mul_one]

theorem beta_r₃ : C.beta (S.t * C.v' * C.w₁' * C.D₁.w₂) = C.F.kF := by
  rw [C.beta_mul C.r₁_mem C.w₂_mem_Q₁, C.beta_r₁, C.beta_w₂, mul_one]

theorem cong_of_alpha_beta {a b : X} (ha : a ∈ C.D₁.Q₁) (hb : b ∈ C.D₁.Q₁)
    (h1 : alpha S a = alpha S b) (h2 : C.beta a = C.beta b) : C.Cong a b := by
  have hc : a * b⁻¹ ∈ C.D₁.Q₁ := mul_mem ha (inv_mem hb)
  have hα : alpha S (a * b⁻¹) = 1 := by
    rw [C.alpha_mul ha (inv_mem hb), C.alpha_inv hb, h1, mul_inv_cancel]
  have hβ : C.beta (a * b⁻¹) = 1 := by
    rw [C.beta_mul ha (inv_mem hb), C.beta_inv hb, h2, mul_inv_cancel]
  exact C.cong_def.mpr (C.mem_E0_of_comm_v' (C.mem_E₁_of_comm_t hc (alpha_eq_one_iff.mp hα))
    (C.beta_eq_one_iff.mp hβ))

theorem r₁_not_mem_E0 : S.t * C.v' * C.w₁' ∉ C.E₀ :=
  C.not_mem_E0_of_alpha (by rw [C.alpha_r₁]; exact C.kz_ne_one)

theorem r₂_not_mem_E0 : S.t * C.v' * C.D₁.w₂ ∉ C.E₀ :=
  C.not_mem_E0_of_alpha (by rw [C.alpha_r₂]; exact C.ky_ne_one)

theorem cong_w₁'_of {n x₀ x₁ : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (hx₀ : x₀ ∈ C.D₁.Q₁)
    (h0 : C.Cong (n * S.t * n⁻¹) x₀) (h1 : C.Cong (n * (S.t * C.v' * C.w₁') * n⁻¹) x₁) :
    C.Cong (n * C.w₁' * n⁻¹) (C.v' * x₀ * x₁) := by
  have e : n * C.w₁' * n⁻¹ = (n * C.v' * n⁻¹)⁻¹ * (n * S.t * n⁻¹)⁻¹ *
      (n * (S.t * C.v' * C.w₁') * n⁻¹) := by group
  have hvQ := C.conj_mem_Q₁ hn C.v'_mem_Q₁
  have htQ := C.conj_mem_Q₁ hn C.t_mem_Q₁
  rw [e]
  refine C.cong_trans (C.cong_mul (mul_mem (inv_mem hvQ) (inv_mem htQ))
    (C.cong_mul (inv_mem hvQ) (C.cong_inv C.v'_mem_Q₁ (C.cong_v' hn)) (C.cong_inv hx₀ h0))
    h1) ?_
  exact C.cong_mul (mul_mem (inv_mem C.v'_mem_Q₁) (inv_mem hx₀))
    (C.cong_mul (inv_mem C.v'_mem_Q₁) (C.cong_self_inv C.v'_mem_Q₁) (C.cong_self_inv hx₀))
    (C.cong_refl _)

theorem cong_w₂_of {n x₀ x₂ : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (hx₀ : x₀ ∈ C.D₁.Q₁)
    (h0 : C.Cong (n * S.t * n⁻¹) x₀) (h2 : C.Cong (n * (S.t * C.v' * C.D₁.w₂) * n⁻¹) x₂) :
    C.Cong (n * C.D₁.w₂ * n⁻¹) (C.v' * x₀ * x₂) := by
  have e : n * C.D₁.w₂ * n⁻¹ = (n * C.v' * n⁻¹)⁻¹ * (n * S.t * n⁻¹)⁻¹ *
      (n * (S.t * C.v' * C.D₁.w₂) * n⁻¹) := by group
  have hvQ := C.conj_mem_Q₁ hn C.v'_mem_Q₁
  have htQ := C.conj_mem_Q₁ hn C.t_mem_Q₁
  rw [e]
  refine C.cong_trans (C.cong_mul (mul_mem (inv_mem hvQ) (inv_mem htQ))
    (C.cong_mul (inv_mem hvQ) (C.cong_inv C.v'_mem_Q₁ (C.cong_v' hn)) (C.cong_inv hx₀ h0))
    h2) ?_
  exact C.cong_mul (mul_mem (inv_mem C.v'_mem_Q₁) (inv_mem hx₀))
    (C.cong_mul (inv_mem C.v'_mem_Q₁) (C.cong_self_inv C.v'_mem_Q₁) (C.cong_self_inv hx₀))
    (C.cong_refl _)

theorem cong_E₁ {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) {r : X} (hr : r ∈ C.D₁.Q₁)
    (hr2 : r ^ 2 ∈ C.E₀) (h : act n C.E₁ = C.E₀ ⊔ zpowers r) : C.Cong (n * S.t * n⁻¹) r :=
  C.cong_of_act hn C.t_not_mem_E0 hr hr2 (by rw [← C.E₁_eq]; exact h)

theorem cong_to_E₁ {n a : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (ha0 : a ∉ C.E₀)
    (h : act n (C.E₀ ⊔ zpowers a) = C.E₁) : C.Cong (n * a * n⁻¹) S.t :=
  C.cong_of_act hn ha0 C.t_mem_Q₁ C.t_sq_mem (by rw [h, C.E₁_eq])

theorem word_K₁ : C.Cong (C.v' * S.t * (S.t * C.v' * C.w₁')) C.w₁' := by
  refine C.cong_of_alpha_beta (mul_mem (mul_mem C.v'_mem_Q₁ C.t_mem_Q₁) C.r₁_mem)
    C.w₁'_mem_Q₁ ?_ ?_
  · rw [C.alpha_mul (mul_mem C.v'_mem_Q₁ C.t_mem_Q₁) C.r₁_mem,
      C.alpha_mul C.v'_mem_Q₁ C.t_mem_Q₁, C.alpha_v', alpha_t S, C.alpha_r₁, C.alpha_w₁',
      mul_one, ← mul_assoc, C.kk, one_mul]
  · rw [C.beta_mul (mul_mem C.v'_mem_Q₁ C.t_mem_Q₁) C.r₁_mem,
      C.beta_mul C.v'_mem_Q₁ C.t_mem_Q₁, C.beta_v', C.beta_t, C.beta_r₁, C.beta_w₁', one_mul,
      C.kk]

theorem word_K₂ : C.Cong (C.v' * S.t * (S.t * C.v' * C.D₁.w₂)) C.D₁.w₂ := by
  refine C.cong_of_alpha_beta (mul_mem (mul_mem C.v'_mem_Q₁ C.t_mem_Q₁) C.r₂_mem)
    C.w₂_mem_Q₁ ?_ ?_
  · rw [C.alpha_mul (mul_mem C.v'_mem_Q₁ C.t_mem_Q₁) C.r₂_mem,
      C.alpha_mul C.v'_mem_Q₁ C.t_mem_Q₁, C.alpha_v', alpha_t S, C.alpha_r₂, C.alpha_w₂,
      mul_one, ← mul_assoc, C.kk, one_mul]
  · rw [C.beta_mul (mul_mem C.v'_mem_Q₁ C.t_mem_Q₁) C.r₂_mem,
      C.beta_mul C.v'_mem_Q₁ C.t_mem_Q₁, C.beta_v', C.beta_t, C.beta_r₂, C.beta_w₂, one_mul,
      C.kk]

theorem word_q₁₁ : C.Cong (C.v' * (S.t * C.v' * C.w₁') * S.t) C.w₁' := by
  refine C.cong_of_alpha_beta (mul_mem (mul_mem C.v'_mem_Q₁ C.r₁_mem) C.t_mem_Q₁)
    C.w₁'_mem_Q₁ ?_ ?_
  · rw [C.alpha_mul (mul_mem C.v'_mem_Q₁ C.r₁_mem) C.t_mem_Q₁,
      C.alpha_mul C.v'_mem_Q₁ C.r₁_mem, C.alpha_v', alpha_t S, C.alpha_r₁, C.alpha_w₁',
      mul_one, ← mul_assoc, C.kk, one_mul]
  · rw [C.beta_mul (mul_mem C.v'_mem_Q₁ C.r₁_mem) C.t_mem_Q₁,
      C.beta_mul C.v'_mem_Q₁ C.r₁_mem, C.beta_v', C.beta_t, C.beta_r₁, C.beta_w₁', one_mul,
      C.kk]

theorem word_q₁₂ : C.Cong (C.v' * (S.t * C.v' * C.w₁') * (S.t * C.v' * C.w₁' * C.D₁.w₂))
    (C.v' * C.D₁.w₂) := by
  refine C.cong_of_alpha_beta (mul_mem (mul_mem C.v'_mem_Q₁ C.r₁_mem) C.r₃_mem)
    (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁) ?_ ?_
  · rw [C.alpha_mul (mul_mem C.v'_mem_Q₁ C.r₁_mem) C.r₃_mem,
      C.alpha_mul C.v'_mem_Q₁ C.r₁_mem, C.alpha_mul C.v'_mem_Q₁ C.w₂_mem_Q₁, C.alpha_v',
      C.alpha_r₁, C.alpha_r₃, C.alpha_w₂, ← mul_assoc C.F.kF C.F.kF, C.kk, one_mul, C.kz,
      ← mul_assoc, ← mul_assoc, zz S, one_mul]
  · rw [C.beta_mul (mul_mem C.v'_mem_Q₁ C.r₁_mem) C.r₃_mem,
      C.beta_mul C.v'_mem_Q₁ C.r₁_mem, C.beta_mul C.v'_mem_Q₁ C.w₂_mem_Q₁, C.beta_v',
      C.beta_r₁, C.beta_r₃, C.beta_w₂, one_mul, one_mul, C.kk]

theorem word_q₂₁ : C.Cong (C.v' * (S.t * C.v' * C.D₁.w₂) * (S.t * C.v' * C.w₁' * C.D₁.w₂))
    (C.v' * C.w₁') := by
  refine C.cong_of_alpha_beta (mul_mem (mul_mem C.v'_mem_Q₁ C.r₂_mem) C.r₃_mem)
    (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁) ?_ ?_
  · rw [C.alpha_mul (mul_mem C.v'_mem_Q₁ C.r₂_mem) C.r₃_mem,
      C.alpha_mul C.v'_mem_Q₁ C.r₂_mem, C.alpha_mul C.v'_mem_Q₁ C.w₁'_mem_Q₁, C.alpha_v',
      C.alpha_r₂, C.alpha_r₃, C.alpha_w₁', ← mul_assoc C.F.kF C.F.kF, C.kk, one_mul]
    calc C.F.yF * (C.F.kF * S.z * C.F.yF) = (C.F.yF * C.F.kF) * S.z * C.F.yF := by group
      _ = (C.F.kF * C.F.yF) * S.z * C.F.yF := by rw [C.ky]
      _ = C.F.kF * (C.F.yF * S.z) * C.F.yF := by group
      _ = C.F.kF * (S.z * C.F.yF) * C.F.yF := by rw [C.yz]
      _ = C.F.kF * S.z * (C.F.yF * C.F.yF) := by group
      _ = C.F.kF * S.z := by rw [C.yy, mul_one]
  · rw [C.beta_mul (mul_mem C.v'_mem_Q₁ C.r₂_mem) C.r₃_mem,
      C.beta_mul C.v'_mem_Q₁ C.r₂_mem, C.beta_mul C.v'_mem_Q₁ C.w₁'_mem_Q₁, C.beta_v',
      C.beta_r₂, C.beta_r₃, C.beta_w₁', one_mul, one_mul, C.kk]

theorem word_q₂₂ : C.Cong (C.v' * (S.t * C.v' * C.D₁.w₂) * S.t) C.D₁.w₂ := by
  refine C.cong_of_alpha_beta (mul_mem (mul_mem C.v'_mem_Q₁ C.r₂_mem) C.t_mem_Q₁)
    C.w₂_mem_Q₁ ?_ ?_
  · rw [C.alpha_mul (mul_mem C.v'_mem_Q₁ C.r₂_mem) C.t_mem_Q₁,
      C.alpha_mul C.v'_mem_Q₁ C.r₂_mem, C.alpha_v', alpha_t S, C.alpha_r₂, C.alpha_w₂,
      mul_one, ← mul_assoc, C.kk, one_mul]
  · rw [C.beta_mul (mul_mem C.v'_mem_Q₁ C.r₂_mem) C.t_mem_Q₁,
      C.beta_mul C.v'_mem_Q₁ C.r₂_mem, C.beta_v', C.beta_t, C.beta_r₂, C.beta_w₂, one_mul,
      C.kk]

theorem cong_K {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (h0 : act n C.E₁ = C.E₁)
    (h1 : act n C.G₁ = C.G₁) (h2 : act n C.G₂ = C.G₂) :
    C.Cong (n * S.t * n⁻¹) S.t ∧ C.Cong (n * C.w₁' * n⁻¹) C.w₁' ∧
      C.Cong (n * C.D₁.w₂ * n⁻¹) C.D₁.w₂ := by
  have ht := C.cong_E₁ hn C.t_mem_Q₁ C.t_sq_mem (by rw [h0, C.E₁_eq])
  have hr₁ := C.cong_of_act hn C.r₁_not_mem_E0 C.r₁_mem C.r₁_sq_mem h1
  have hr₂ := C.cong_of_act hn C.r₂_not_mem_E0 C.r₂_mem C.r₂_sq_mem h2
  exact ⟨ht, C.cong_trans (C.cong_w₁'_of hn C.t_mem_Q₁ ht hr₁) C.word_K₁,
    C.cong_trans (C.cong_w₂_of hn C.t_mem_Q₁ ht hr₂) C.word_K₂⟩

theorem cong_q₁ {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (h0 : act n C.E₁ = C.G₁)
    (h1 : act n C.G₁ = C.E₁) (h2 : act n C.G₂ = C.G₃) :
    C.Cong (n * S.t * n⁻¹) (S.t * C.v' * C.w₁') ∧ C.Cong (n * C.w₁' * n⁻¹) C.w₁' ∧
      C.Cong (n * C.D₁.w₂ * n⁻¹) (C.v' * C.D₁.w₂) := by
  have ht := C.cong_E₁ hn C.r₁_mem C.r₁_sq_mem h0
  have hr₁ := C.cong_to_E₁ hn C.r₁_not_mem_E0 h1
  have hr₂ := C.cong_of_act hn C.r₂_not_mem_E0 C.r₃_mem C.r₃_sq_mem h2
  exact ⟨ht, C.cong_trans (C.cong_w₁'_of hn C.r₁_mem ht hr₁) C.word_q₁₁,
    C.cong_trans (C.cong_w₂_of hn C.r₁_mem ht hr₂) C.word_q₁₂⟩

theorem cong_q₂ {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (h0 : act n C.E₁ = C.G₂)
    (h1 : act n C.G₁ = C.G₃) (h2 : act n C.G₂ = C.E₁) :
    C.Cong (n * S.t * n⁻¹) (S.t * C.v' * C.D₁.w₂) ∧ C.Cong (n * C.w₁' * n⁻¹) (C.v' * C.w₁') ∧
      C.Cong (n * C.D₁.w₂ * n⁻¹) C.D₁.w₂ := by
  have ht := C.cong_E₁ hn C.r₂_mem C.r₂_sq_mem h0
  have hr₁ := C.cong_of_act hn C.r₁_not_mem_E0 C.r₃_mem C.r₃_sq_mem h1
  have hr₂ := C.cong_to_E₁ hn C.r₂_not_mem_E0 h2
  exact ⟨ht, C.cong_trans (C.cong_w₁'_of hn C.r₂_mem ht hr₁) C.word_q₂₁,
    C.cong_trans (C.cong_w₂_of hn C.r₂_mem ht hr₂) C.word_q₂₂⟩

theorem w₁'_sq_exc : C.w₁' ^ 2 = S.z * C.F.kF := by
  have h := C.D₁.q0_holds
  rw [C.exc] at h
  rw [C.w₁'_sq]; exact h.1

theorem w₂_sq_exc : C.D₁.w₂ ^ 2 = C.F.yF * C.F.kF := by
  have h := C.D₁.q0_holds
  rw [C.exc] at h
  exact h.2.1

theorem sq_tw₁' : (S.t * C.w₁') ^ 2 = C.F.kF := by
  rw [C.sq_t_mul_eq C.w₁'_mem_Q₁, C.alpha_w₁', C.w₁'_sq_exc, ← mul_assoc, zz S, one_mul]

theorem sq_tw₂ : (S.t * C.D₁.w₂) ^ 2 = C.F.kF := by
  rw [C.sq_t_mul_eq C.w₂_mem_Q₁, C.alpha_w₂, C.w₂_sq_exc, ← mul_assoc, C.yy, one_mul]

theorem conj_E0_fix {n x₀ x₁ x₂ : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X))
    (hx₀ : x₀ ∈ C.D₁.Q₁) (hx₁ : x₁ ∈ C.D₁.Q₁) (hx₂ : x₂ ∈ C.D₁.Q₁)
    (h0 : C.Cong (n * S.t * n⁻¹) x₀) (h1 : C.Cong (n * C.w₁' * n⁻¹) x₁)
    (h2 : C.Cong (n * C.D₁.w₂ * n⁻¹) x₂) (s0 : (x₀ * C.v') ^ 2 = C.F.kF)
    (s1 : (C.v' * x₁) ^ 2 = S.z * C.F.kF) (s2 : (C.v' * x₂) ^ 2 = C.F.yF * C.F.kF) :
    ∀ e ∈ C.E₀, n * e * n⁻¹ = e := by
  have hv := C.cong_v' hn
  have hvQ := C.conj_mem_Q₁ hn C.v'_mem_Q₁
  have hk : n * C.F.kF * n⁻¹ = C.F.kF := by
    have e : n * C.F.kF * n⁻¹ = ((n * S.t * n⁻¹) * (n * C.v' * n⁻¹)) ^ 2 := by
      rw [← C.sq_tv', pow_two, pow_two]; group
    rw [e, C.sq_of_coset (mul_mem hx₀ C.v'_mem_Q₁)
      (C.cong_def.mp (C.cong_mul (C.conj_mem_Q₁ hn C.t_mem_Q₁) h0 hv)), s0]
  have hzk : n * (S.z * C.F.kF) * n⁻¹ = S.z * C.F.kF := by
    have e : n * (S.z * C.F.kF) * n⁻¹ = ((n * C.v' * n⁻¹) * (n * C.w₁' * n⁻¹)) ^ 2 := by
      rw [← C.sq_v'w₁', pow_two, pow_two]; group
    rw [e, C.sq_of_coset (mul_mem C.v'_mem_Q₁ hx₁) (C.cong_def.mp (C.cong_mul hvQ hv h1)), s1]
  have hyk : n * (C.F.yF * C.F.kF) * n⁻¹ = C.F.yF * C.F.kF := by
    have e : n * (C.F.yF * C.F.kF) * n⁻¹ = ((n * C.v' * n⁻¹) * (n * C.D₁.w₂ * n⁻¹)) ^ 2 := by
      rw [← C.sq_v'w₂, pow_two, pow_two]; group
    rw [e, C.sq_of_coset (mul_mem C.v'_mem_Q₁ hx₂) (C.cong_def.mp (C.cong_mul hvQ hv h2)), s2]
  have hz : n * S.z * n⁻¹ = S.z := by
    have := hzk
    rw [conj_mul_eq, hk] at this
    exact mul_right_cancel this
  have hy : n * C.F.yF * n⁻¹ = C.F.yF := by
    have := hyk
    rw [conj_mul_eq, hk] at this
    exact mul_right_cancel this
  have hle : C.E₀ ≤ centralizer ({n} : Set X) := by
    show closure {S.z, C.F.yF, C.F.kF} ≤ _
    rw [closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hc : ∀ {a : X}, n * a * n⁻¹ = a → a * n = n * a := fun {a} h => by
      calc a * n = (n * a * n⁻¹) * n := by rw [h]
        _ = n * a := by group
    rcases he with rfl | rfl | rfl
    · exact hc hz
    · exact hc hy
    · exact hc hk
  intro e he
  have := mem_centralizer_singleton_iff.mp (hle he)
  rw [← this, mul_inv_cancel_right]

theorem conj_E0_K {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (h0 : act n C.E₁ = C.E₁)
    (h1 : act n C.G₁ = C.G₁) (h2 : act n C.G₂ = C.G₂) : ∀ e ∈ C.E₀, n * e * n⁻¹ = e := by
  obtain ⟨c0, c1, c2⟩ := C.cong_K hn h0 h1 h2
  exact C.conj_E0_fix hn C.t_mem_Q₁ C.w₁'_mem_Q₁ C.w₂_mem_Q₁ c0 c1 c2 C.sq_tv' C.sq_v'w₁'
    C.sq_v'w₂

theorem sq_r₁v' : (S.t * C.v' * C.w₁' * C.v') ^ 2 = C.F.kF := by
  refine (C.sq_of_coset (mul_mem C.t_mem_Q₁ C.w₁'_mem_Q₁) (C.cong_def.mp ?_)).trans C.sq_tw₁'
  refine C.cong_of_alpha_beta (mul_mem C.r₁_mem C.v'_mem_Q₁)
    (mul_mem C.t_mem_Q₁ C.w₁'_mem_Q₁) ?_ ?_
  · rw [C.alpha_mul C.r₁_mem C.v'_mem_Q₁, C.alpha_mul C.t_mem_Q₁ C.w₁'_mem_Q₁, C.alpha_r₁,
      C.alpha_v', alpha_t S, C.alpha_w₁', one_mul, C.kz, mul_assoc, C.kk, mul_one]
  · rw [C.beta_mul C.r₁_mem C.v'_mem_Q₁, C.beta_mul C.t_mem_Q₁ C.w₁'_mem_Q₁, C.beta_r₁,
      C.beta_v', C.beta_t, C.beta_w₁']

theorem sq_r₂v' : (S.t * C.v' * C.D₁.w₂ * C.v') ^ 2 = C.F.kF := by
  refine (C.sq_of_coset (mul_mem C.t_mem_Q₁ C.w₂_mem_Q₁) (C.cong_def.mp ?_)).trans C.sq_tw₂
  refine C.cong_of_alpha_beta (mul_mem C.r₂_mem C.v'_mem_Q₁)
    (mul_mem C.t_mem_Q₁ C.w₂_mem_Q₁) ?_ ?_
  · rw [C.alpha_mul C.r₂_mem C.v'_mem_Q₁, C.alpha_mul C.t_mem_Q₁ C.w₂_mem_Q₁, C.alpha_r₂,
      C.alpha_v', alpha_t S, C.alpha_w₂, one_mul, C.ky, mul_assoc, C.kk, mul_one]
  · rw [C.beta_mul C.r₂_mem C.v'_mem_Q₁, C.beta_mul C.t_mem_Q₁ C.w₂_mem_Q₁, C.beta_r₂,
      C.beta_v', C.beta_t, C.beta_w₂]

theorem conj_E0_q₁ {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (h0 : act n C.E₁ = C.G₁)
    (h1 : act n C.G₁ = C.E₁) (h2 : act n C.G₂ = C.G₃) : ∀ e ∈ C.E₀, n * e * n⁻¹ = e := by
  obtain ⟨c0, c1, c2⟩ := C.cong_q₁ hn h0 h1 h2
  exact C.conj_E0_fix hn C.r₁_mem C.w₁'_mem_Q₁ (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁) c0 c1 c2
    C.sq_r₁v' C.sq_v'w₁' (by rw [← mul_assoc, C.v'v', one_mul, C.w₂_sq_exc])

theorem conj_E0_q₂ {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (h0 : act n C.E₁ = C.G₂)
    (h1 : act n C.G₁ = C.G₃) (h2 : act n C.G₂ = C.E₁) : ∀ e ∈ C.E₀, n * e * n⁻¹ = e := by
  obtain ⟨c0, c1, c2⟩ := C.cong_q₂ hn h0 h1 h2
  exact C.conj_E0_fix hn C.r₂_mem (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁) C.w₂_mem_Q₁ c0 c1 c2
    C.sq_r₂v' (by rw [← mul_assoc, C.v'v', one_mul, C.w₁'_sq_exc]) C.sq_v'w₂

theorem S₁_eq_sup : C.D₁.S₁ = C.D₁.Q₁ ⊔ zpowers C.D₁.u := by
  have hle : C.D₁.Q₁ ⊔ zpowers C.D₁.u ≤ C.D₁.S₁ :=
    sup_le C.Q₁_le_S₁ (zpowers_le.mpr C.u_mem_S₁)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_sup_zpowers_eq C.u_normalizes (by rw [pow_two, C.u_mul_u]; exact one_mem _)
    (u_not_mem_Q₁ C.isRefl_y C.D₁), C.card_Q₁]
  exact card_S₁_le C.isRefl_y C.D₁

theorem act_Q₁ {a r : X} (ha : a ∈ C.D₁.Q₁) (hr : r ∈ C.D₁.Q₁) :
    act a (C.E₀ ⊔ zpowers r) = C.E₀ ⊔ zpowers r := by
  rw [act, C.map_sup_zpowers (le_normalizer ha)]
  exact C.sup_zpowers_eq_of_coset (by
    rw [show a * r * a⁻¹ * r⁻¹ = a * r * a⁻¹ * r⁻¹ from rfl]; exact C.comm_mem_E0 ha hr)

theorem mem_Q₁_of_fix {s : X} (hs : s ∈ C.S₂) (h0 : act s C.E₁ = C.E₁)
    (h2 : act s C.G₂ = C.G₂) : s ∈ C.D₁.Q₁ := by
  have hS₁ : s ∈ C.D₁.S₁ := by
    rw [← C.S₂_inf]; exact ⟨hs, mem_normalizer_of_map_eq h0⟩
  rw [C.S₁_eq_sup] at hS₁
  rcases mem_or_of_mem_sup_zpowers C.u_normalizes
    (by rw [pow_two, C.u_mul_u]; exact one_mem _) hS₁ with h | h
  · exact h
  · exfalso
    apply C.G₂_ne_G₃
    rw [← h2, show s = s * C.D₁.u⁻¹ * C.D₁.u by group, act_mul, C.u_G₂', C.act_Q₁ h C.r₃_mem]

theorem sq_mem_Q₁_of {s : X} (hs : s ∈ C.S₂) (h0 : act s (act s C.E₁) = C.E₁)
    (h2 : act s (act s C.G₂) = C.G₂) : s ^ 2 ∈ C.D₁.Q₁ :=
  C.mem_Q₁_of_fix (pow_mem hs 2) (by rw [pow_two, act_mul, h0]) (by rw [pow_two, act_mul, h2])

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
