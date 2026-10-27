module

public import CFSG.ClassicalInvolution.Phan.PhanQ5Split

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section KData

variable {F K : Type} [Field F] [Field K] [Algebra F K]

structure KData (F K : Type) [Field F] [Field K] [Algebra F K] (ε : F) where
  τ : K →+* K
  tau_alg : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a
  tau_tau : ∀ x : K, τ (τ x) = x
  tau_pow : ∀ x : K, τ x = x ^ Nat.card F
  card_K : Nat.card K = Nat.card F ^ 2
  fixed : ∀ x : K, τ x = x → ∃ a : F, algebraMap F K a = x
  θ : K
  theta_sq : θ ^ 2 = algebraMap F K (-(1 / ε))
  tau_theta : τ θ = -θ

variable {ε : F} (D : KData F K ε)

@[expose] def conj (v : V8 K) : V8 K := fun i => D.τ (v i)

theorem conj_conj (v : V8 K) : conj D (conj D v) = v := by
  ext i
  exact D.tau_tau (v i)

theorem conj_add (u v : V8 K) : conj D (u + v) = conj D u + conj D v := by
  ext i
  simp [conj]

theorem conj_smul (κ : K) (v : V8 K) : conj D (κ • v) = D.τ κ • conj D v := by
  ext i
  simp [conj]

theorem B8_eq_sum (u v : V8 K) :
    B8 u v = ∑ i : Fin 4, (u (Sum.inl i) * v (Sum.inr i) + v (Sum.inl i) * u (Sum.inr i)) :=
  polar_quadPlus 4 K u v

theorem Q8_eq_sum (v : V8 K) : Q8 v = ∑ i : Fin 4, v (Sum.inl i) * v (Sum.inr i) :=
  quadPlus_apply 4 K v

theorem B8_conj (u v : V8 K) : B8 (conj D u) (conj D v) = D.τ (B8 u v) := by
  rw [B8_eq_sum, B8_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [conj]

theorem Q8_conj (v : V8 K) : Q8 (conj D v) = D.τ (Q8 v) := by
  rw [Q8_eq_sum, Q8_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [conj]

@[expose] noncomputable def her (u v : V8 K) : K := B8 u (conj D v)

theorem her_conj_symm (u v : V8 K) : her D v u = D.τ (her D u v) := by
  rw [her, her, ← B8_conj D, conj_conj, B8_comm]

theorem her_smul_left (κ : K) (u v : V8 K) : her D (κ • u) v = κ * her D u v := by
  rw [her, her, B8_smul_left]

theorem her_smul_right (κ : K) (u v : V8 K) : her D u (κ • v) = D.τ κ * her D u v := by
  rw [her, her, conj_smul, B8_smul_right]

theorem her_add_left (u v w : V8 K) : her D (u + v) w = her D u w + her D v w := by
  rw [her, her, her, B8_add_left]

theorem her_add_right (u v w : V8 K) : her D w (u + v) = her D w u + her D w v := by
  rw [her, her, her, conj_add, B8_add_right]

theorem her_self_fixed (u : V8 K) : D.τ (her D u u) = her D u u := by
  rw [← her_conj_symm]

@[expose] noncomputable def ffK (v : V8 K) : Prop := Q8 v = 0 ∧ her D v v ≠ 0

@[expose] noncomputable def gram (u v : V8 K) : K := her D u u * her D v v - her D u v * her D v u

@[expose] noncomputable def ColK (u v : V8 K) : Prop := B8 u v = 0 ∧ gram D u v ≠ 0

theorem gram_comm (u v : V8 K) : gram D v u = gram D u v := by
  unfold gram
  ring

theorem ColK.symm {u v : V8 K} (h : ColK D u v) : ColK D v u :=
  ⟨by rw [B8_comm]; exact h.1, by rw [gram_comm]; exact h.2⟩

theorem gram_smul (κ κ' : K) (u v : V8 K) :
    gram D (κ • u) (κ' • v) = (κ * D.τ κ) * (κ' * D.τ κ') * gram D u v := by
  unfold gram
  rw [her_smul_left, her_smul_right, her_smul_left, her_smul_right, her_smul_left,
    her_smul_right, her_smul_left, her_smul_right]
  ring

theorem norm_ne_zero {κ : K} (hκ : κ ≠ 0) : κ * D.τ κ ≠ 0 := by
  refine mul_ne_zero hκ fun h => hκ ?_
  have := congrArg D.τ h
  rwa [D.tau_tau, map_zero] at this

theorem colK_smul {κ κ' : K} (hκ : κ ≠ 0) (hκ' : κ' ≠ 0) {u v : V8 K} :
    ColK D (κ • u) (κ' • v) ↔ ColK D u v := by
  unfold ColK
  rw [B8_smul_left, B8_smul_right, gram_smul]
  have h1 := norm_ne_zero D hκ
  have h2 := norm_ne_zero D hκ'
  constructor
  · rintro ⟨a, b⟩
    refine ⟨?_, fun h => b ?_⟩
    · rcases mul_eq_zero.1 a with h | h
      · exact absurd h hκ
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hκ'
        · exact h
    · rw [h, mul_zero]
  · rintro ⟨a, b⟩
    exact ⟨by rw [a, mul_zero, mul_zero], mul_ne_zero (mul_ne_zero h1 h2) b⟩

end KData

end CFSG.ClassicalInvolution.PhanQ
