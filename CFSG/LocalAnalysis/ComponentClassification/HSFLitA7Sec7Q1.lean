module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Core
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Three

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_of_map_le [Finite X] {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set X) := by
  refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge h ?_)
  rw [card_map_of_injective (MulAut.conj g).injective]

omit [Finite X] in
theorem map_conj_sup_le {A B H : Subgroup X} {g : X} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ H)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ H) : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ H := by
  rw [map_le_iff_le_comap]
  exact sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)

omit [Finite X] in
theorem conj_zpowers_mem {H : Subgroup X} {g b : X} (hb : g * b * g⁻¹ ∈ H) :
    ∀ c ∈ zpowers b, g * c * g⁻¹ ∈ H := by
  intro c hc
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc
  rw [← conj_zpow]
  exact zpow_mem hb n

omit [Finite X] in
theorem sq_mul_eq {a b : X} (h : a * (b * a * b⁻¹ * a⁻¹) = (b * a * b⁻¹ * a⁻¹) * a) :
    (a * b) ^ 2 = (b * a * b⁻¹ * a⁻¹) * a ^ 2 * b ^ 2 := by
  rw [pow_two, pow_two, pow_two,
    show a * b * (a * b) = a * (b * a * b⁻¹ * a⁻¹) * a * (b * b) by group, h]
  group

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem w₁'_comm_E0 {e : X} (he : e ∈ C.E₀) : C.w₁' * e = e * C.w₁' := by
  have := C.w₁'_E0 he
  calc C.w₁' * e = C.w₁' * e * C.w₁'⁻¹ * C.w₁' := by group
    _ = e * C.w₁' := by rw [this]

theorem w₂_comm_E0 {e : X} (he : e ∈ C.E₀) : C.D₁.w₂ * e = e * C.D₁.w₂ := by
  have := C.w₂_E0 he
  calc C.D₁.w₂ * e = C.D₁.w₂ * e * C.D₁.w₂⁻¹ * C.D₁.w₂ := by group
    _ = e * C.D₁.w₂ := by rw [this]

theorem comm_w₁'w₂ : C.w₁' * C.D₁.w₂ * C.w₁'⁻¹ * C.D₁.w₂⁻¹ = C.F.kF := by
  rcases C.w₁'_eq with h | h <;> rw [h]
  · exact C.comm_w₁w₂
  · have hk := C.comm_w₁w₂
    rw [show C.F.yF * C.D₁.w₁ * C.D₁.w₂ * (C.F.yF * C.D₁.w₁)⁻¹ * C.D₁.w₂⁻¹ =
      C.F.yF * (C.D₁.w₁ * C.D₁.w₂ * C.D₁.w₁⁻¹ * C.D₁.w₂⁻¹) * (C.D₁.w₂ * C.F.yF⁻¹ * C.D₁.w₂⁻¹)
        by group, hk, show C.D₁.w₂ * C.F.yF⁻¹ * C.D₁.w₂⁻¹ = C.F.yF⁻¹ by
          rw [show C.D₁.w₂ * C.F.yF⁻¹ * C.D₁.w₂⁻¹ = (C.D₁.w₂ * C.F.yF * C.D₁.w₂⁻¹)⁻¹ by group,
            C.w₂_E0 C.y_mem_E0],
      conj_eq_of_comm (C.comm_E0 C.y_mem_E0 C.k_mem_E0)]

theorem w₂_w₁' : C.D₁.w₂ * C.w₁' * C.D₁.w₂⁻¹ = C.F.kF * C.w₁' := by
  have h := C.comm_w₁'w₂
  have hkinv : C.F.kF⁻¹ = C.F.kF := inv_eq_of_mul_eq_one_right C.kk
  calc C.D₁.w₂ * C.w₁' * C.D₁.w₂⁻¹ =
        (C.w₁' * C.D₁.w₂ * C.w₁'⁻¹ * C.D₁.w₂⁻¹)⁻¹ * C.w₁' := by group
    _ = C.F.kF * C.w₁' := by rw [h, hkinv]

theorem w₂_v'_cases : (C.D₁.q0 = .e4q8 ∧ C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ = C.F.yF * C.v') ∨
    (C.D₁.q0 = .exceptional ∧ C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ = C.v') := by
  rcases C.hq with hq | hq
  · left
    refine ⟨hq, ?_⟩
    have h := C.v't_comm_Q0 hq C.w₂_mem_Q0
    have h1 : C.D₁.w₂ * (C.v' * S.t) * C.D₁.w₂⁻¹ = C.v' * S.t := by rw [← h, mul_inv_cancel_right]
    rw [conj_mul_eq, C.w₂_t] at h1
    calc C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ = C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * (S.t * C.F.yF) *
          (S.t * C.F.yF)⁻¹ := by group
      _ = C.v' * S.t * (C.F.yF⁻¹ * S.t⁻¹) := by rw [h1]; group
      _ = C.F.yF * C.v' := by
        rw [show C.F.yF⁻¹ = C.F.yF from inv_eq_of_mul_eq_one_right C.yy, t_inv S,
          ← C.isRefl_y.comm_E0_t C.isK_k C.y_mem_E0, ← mul_assoc, mul_assoc C.v', tt S,
          mul_one, C.comm_v'_E0 C.y_mem_E0]
  · right
    refine ⟨hq, ?_⟩
    rw [← C.v'_comm_Q0 hq C.w₂_mem_Q0, mul_inv_cancel_right]

theorem c₂_mem : C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * C.v'⁻¹ ∈ C.E₀ := by
  rcases C.w₂_v'_cases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
  · rw [mul_inv_cancel_right]; exact C.y_mem_E0
  · rw [mul_inv_cancel]; exact one_mem _

theorem c₁_mem : C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹ ∈ C.E₀ :=
  zpowers_le.mpr C.z_mem_E0 C.comm_w₁'_v'_mem

def Tm (W : Subgroup X) (hW : W ≤ C.E₀) : Subgroup X where
  carrier := {p | (∀ e ∈ C.E₀, p * e * p⁻¹ = e) ∧ S.t⁻¹ * (p * S.t * p⁻¹) ∈ W}
  mul_mem' := by
    rintro p q ⟨hp, hpt⟩ ⟨hq, hqt⟩
    refine ⟨fun e he => ?_, ?_⟩
    · calc p * q * e * (p * q)⁻¹ = p * (q * e * q⁻¹) * p⁻¹ := by group
        _ = e := by rw [hq e he, hp e he]
    · have h1 : p * q * S.t * (p * q)⁻¹ = (p * S.t * p⁻¹) *
          (p * (S.t⁻¹ * (q * S.t * q⁻¹)) * p⁻¹) := by group
      rw [h1, hp _ (hW hqt)]
      rw [show S.t⁻¹ * (p * S.t * p⁻¹ * (S.t⁻¹ * (q * S.t * q⁻¹))) =
        (S.t⁻¹ * (p * S.t * p⁻¹)) * (S.t⁻¹ * (q * S.t * q⁻¹)) by group]
      exact mul_mem hpt hqt
  one_mem' := by
    refine ⟨fun e _ => by group, ?_⟩
    rw [show S.t⁻¹ * (1 * S.t * 1⁻¹) = 1 by group]
    exact one_mem _
  inv_mem' := by
    rintro p ⟨hp, hpt⟩
    have hp' : ∀ e ∈ C.E₀, p⁻¹ * e * p⁻¹⁻¹ = e := fun e he => by
      calc p⁻¹ * e * p⁻¹⁻¹ = p⁻¹ * (p * e * p⁻¹) * p := by rw [hp e he, inv_inv]
        _ = e := by group
    refine ⟨hp', ?_⟩
    have h1 := hp' _ (hW hpt)
    have : S.t⁻¹ * (p⁻¹ * S.t * p⁻¹⁻¹) = (p⁻¹ * (S.t⁻¹ * (p * S.t * p⁻¹)) * p⁻¹⁻¹)⁻¹ := by
      group
    rw [this, h1]
    exact inv_mem hpt

theorem mem_Tm {W : Subgroup X} {hW : W ≤ C.E₀} {p : X} :
    p ∈ C.Tm W hW ↔ (∀ e ∈ C.E₀, p * e * p⁻¹ = e) ∧ S.t⁻¹ * (p * S.t * p⁻¹) ∈ W := Iff.rfl

theorem E0_le_Tm (W : Subgroup X) (hW : W ≤ C.E₀) : C.E₀ ≤ C.Tm W hW := by
  intro e he
  refine ⟨fun f hf => conj_eq_of_comm (C.comm_E0 he hf), ?_⟩
  rw [conj_eq_of_comm (C.t_comm_E0 he).symm, inv_mul_cancel]
  exact one_mem _

theorem t_mem_Tm (W : Subgroup X) (hW : W ≤ C.E₀) : S.t ∈ C.Tm W hW := by
  refine ⟨fun e he => conj_eq_of_comm (C.t_comm_E0 he), ?_⟩
  rw [mul_inv_cancel_right, inv_mul_cancel]
  exact one_mem _

theorem v'_mem_Tm {W : Subgroup X} {hW : W ≤ C.E₀} (hk : C.F.kF ∈ W) : C.v' ∈ C.Tm W hW :=
  ⟨fun e he => C.v'_E0 he, by rw [C.v'_t, inv_mul_cancel_left]; exact hk⟩

theorem w₁'_mem_Tm {W : Subgroup X} {hW : W ≤ C.E₀} (hz : S.z ∈ W) : C.w₁' ∈ C.Tm W hW :=
  ⟨fun e he => C.w₁'_E0 he, by rw [C.w₁'_t, inv_mul_cancel_left]; exact hz⟩

theorem w₂_mem_Tm {W : Subgroup X} {hW : W ≤ C.E₀} (hy : C.F.yF ∈ W) : C.D₁.w₂ ∈ C.Tm W hW :=
  ⟨fun e he => C.w₂_E0 he, by rw [C.w₂_t, inv_mul_cancel_left]; exact hy⟩

abbrev E₁ : Subgroup X := S.E C.F.yF

theorem E₁_eq : C.E₁ = C.E₀ ⊔ zpowers S.t := C.isRefl_y.E_eq_E0_sup C.isK_k

abbrev P₂ : Subgroup X := C.E₁ ⊔ zpowers C.v'

abbrev P₃ : Subgroup X := C.P₂ ⊔ zpowers C.w₁'

abbrev Q₁' : Subgroup X := C.P₃ ⊔ zpowers C.D₁.w₂

theorem zk_le_E0 : (zpowers S.z ⊔ zpowers C.F.kF : Subgroup X) ≤ C.E₀ :=
  sup_le (zpowers_le.mpr C.z_mem_E0) (zpowers_le.mpr C.k_mem_E0)

theorem kpow_le_E0 : zpowers C.F.kF ≤ C.E₀ := zpowers_le.mpr C.k_mem_E0

theorem E₁_le_Tm (W : Subgroup X) (hW : W ≤ C.E₀) : C.E₁ ≤ C.Tm W hW := by
  rw [C.E₁_eq]
  exact sup_le (C.E0_le_Tm W hW) (zpowers_le.mpr (C.t_mem_Tm W hW))

theorem P₂_le_Tm : C.P₂ ≤ C.Tm (zpowers C.F.kF) C.kpow_le_E0 :=
  sup_le (C.E₁_le_Tm _ _) (zpowers_le.mpr (C.v'_mem_Tm (mem_zpowers _)))

theorem P₃_le_Tm : C.P₃ ≤ C.Tm (zpowers S.z ⊔ zpowers C.F.kF) C.zk_le_E0 :=
  sup_le (sup_le (C.E₁_le_Tm _ _) (zpowers_le.mpr (C.v'_mem_Tm (mem_sup_right (mem_zpowers _)))))
    (zpowers_le.mpr (C.w₁'_mem_Tm (mem_sup_left (mem_zpowers _))))

theorem Q₁'_le_Tm : C.Q₁' ≤ C.Tm C.E₀ le_rfl :=
  sup_le (sup_le (sup_le (C.E₁_le_Tm _ _) (zpowers_le.mpr (C.v'_mem_Tm C.k_mem_E0)))
    (zpowers_le.mpr (C.w₁'_mem_Tm C.z_mem_E0))) (zpowers_le.mpr (C.w₂_mem_Tm C.y_mem_E0))

theorem t_mem_E₁ : S.t ∈ C.E₁ := t_mem_E _

theorem E0_le_E₁ : C.E₀ ≤ C.E₁ := E0_le_E C.isK_k _

theorem v'_not_mem_E₁ : C.v' ∉ C.E₁ := by
  intro h
  have := (C.E₁_le_Tm ⊥ bot_le h).2
  rw [C.v'_t, inv_mul_cancel_left, mem_bot] at this
  exact C.isK_k.ne_one this

theorem w₁'_not_mem_P₂ : C.w₁' ∉ C.P₂ := by
  intro h
  have := (C.P₂_le_Tm h).2
  rw [C.w₁'_t, inv_mul_cancel_left] at this
  exact C.k_not_mem_zpowers_z (by
    rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq this with h1 | h1
    · exact absurd h1 S.z_ne_one
    · rw [← h1]; exact mem_zpowers _)

theorem w₂_not_mem_P₃ : C.D₁.w₂ ∉ C.P₃ := by
  intro h
  have := (C.P₃_le_Tm h).2
  rw [C.w₂_t, inv_mul_cancel_left] at this
  exact C.isRefl_y.not_mem_B (zk_le_B C.isK_k this)

theorem E0_le_P₂ : C.E₀ ≤ C.P₂ := C.E0_le_E₁.trans le_sup_left

theorem E0_le_P₃ : C.E₀ ≤ C.P₃ := C.E0_le_P₂.trans le_sup_left

theorem E0_le_Q₁' : C.E₀ ≤ C.Q₁' := C.E0_le_P₃.trans le_sup_left

theorem v'_normalizes_E₁ : C.v' ∈ normalizer (C.E₁ : Set X) := by
  refine mem_normalizer_of_map_le ?_
  rw [C.E₁_eq]
  refine map_conj_sup_le (fun e he => ?_) (conj_zpowers_mem ?_)
  · rw [C.v'_E0 he]; exact mem_sup_left he
  · rw [C.v'_t]; exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left C.k_mem_E0)

theorem w₁'_normalizes_P₂ : C.w₁' ∈ normalizer (C.P₂ : Set X) := by
  refine mem_normalizer_of_map_le (map_conj_sup_le (fun e he => ?_) (conj_zpowers_mem ?_))
  · rw [C.E₁_eq] at he
    have hle : (C.E₀ ⊔ zpowers S.t).map (MulAut.conj C.w₁').toMonoidHom ≤ C.P₂ := by
      refine map_conj_sup_le (fun f hf => ?_) (conj_zpowers_mem ?_)
      · rw [C.w₁'_E0 hf]; exact C.E0_le_P₂ hf
      · rw [C.w₁'_t]
        exact mul_mem (mem_sup_left C.t_mem_E₁) (C.E0_le_P₂ C.z_mem_E0)
    exact hle ⟨e, he, rfl⟩
  · rw [show C.w₁' * C.v' * C.w₁'⁻¹ = (C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹) * C.v' by group]
    exact mul_mem (C.E0_le_P₂ C.c₁_mem) (mem_sup_right (mem_zpowers _))

theorem w₂_normalizes_P₃ : C.D₁.w₂ ∈ normalizer (C.P₃ : Set X) := by
  refine mem_normalizer_of_map_le (map_conj_sup_le (fun p hp => ?_) (conj_zpowers_mem ?_))
  · have hle : C.P₂.map (MulAut.conj C.D₁.w₂).toMonoidHom ≤ C.P₃ := by
      refine map_conj_sup_le (fun e he => ?_) (conj_zpowers_mem ?_)
      · rw [C.E₁_eq] at he
        have hle' : (C.E₀ ⊔ zpowers S.t).map (MulAut.conj C.D₁.w₂).toMonoidHom ≤ C.P₃ := by
          refine map_conj_sup_le (fun f hf => ?_) (conj_zpowers_mem ?_)
          · rw [C.w₂_E0 hf]; exact C.E0_le_P₃ hf
          · rw [C.w₂_t]
            exact mul_mem (mem_sup_left (mem_sup_left C.t_mem_E₁)) (C.E0_le_P₃ C.y_mem_E0)
        exact hle' ⟨e, he, rfl⟩
      · rw [show C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ = (C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * C.v'⁻¹) * C.v' by
          group]
        exact mul_mem (C.E0_le_P₃ C.c₂_mem) (mem_sup_left (mem_sup_right (mem_zpowers _)))
    exact hle ⟨p, hp, rfl⟩
  · rw [C.w₂_w₁']
    exact mul_mem (C.E0_le_P₃ C.k_mem_E0) (mem_sup_right (mem_zpowers _))

theorem v'_sq_mem : C.v' ^ 2 ∈ C.E₁ := by rw [C.v'_sq]; exact one_mem _

theorem w₁'_sq_mem_E0 : C.w₁' ^ 2 ∈ C.E₀ := by rw [C.w₁'_sq]; exact C.w₁_sq_mem

theorem card_E₁ : Nat.card C.E₁ = 16 := C.isRefl_y.card_E

theorem card_P₂ : Nat.card C.P₂ = 32 := by
  rw [card_sup_zpowers_eq C.v'_normalizes_E₁ C.v'_sq_mem C.v'_not_mem_E₁, C.card_E₁]

theorem card_P₃ : Nat.card C.P₃ = 64 := by
  rw [card_sup_zpowers_eq C.w₁'_normalizes_P₂ (C.E0_le_P₂ C.w₁'_sq_mem_E0) C.w₁'_not_mem_P₂,
    C.card_P₂]

theorem card_Q₁' : Nat.card C.Q₁' = 128 := by
  rw [card_sup_zpowers_eq C.w₂_normalizes_P₃ (C.E0_le_P₃ C.w₂_sq_mem) C.w₂_not_mem_P₃, C.card_P₃]

theorem Q₁'_le : C.Q₁' ≤ C.D₁.Q₁ := by
  have hQ0 : C.Q₀ ≤ C.D₁.Q₁ := C.D₁.Q0_le
  have hC : C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) ≤ C.D₁.Q₁ := inf_le_left
  refine sup_le (sup_le (sup_le ?_ (zpowers_le.mpr (hC C.v'_mem_C)))
    (zpowers_le.mpr (hQ0 C.w₁'_mem_Q0))) (zpowers_le.mpr (hQ0 C.w₂_mem_Q0))
  rw [C.E₁_eq]
  exact sup_le (C.E0_le_Q0.trans hQ0) (zpowers_le.mpr (hC (t_mem_C C.D₁)))

theorem Q₁_eq : C.D₁.Q₁ = C.Q₁' :=
  (Subgroup.eq_of_le_of_card_ge C.Q₁'_le (by rw [C.card_Q₁']; exact card_Q₁_le C.isRefl_y C.D₁))
    |>.symm

theorem card_Q₁ : Nat.card C.D₁.Q₁ = 128 := by rw [C.Q₁_eq, C.card_Q₁']

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
