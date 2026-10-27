module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abSide2

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace ISide

variable (V : ISide S T₁)

theorem elemAbelianTwo_ki : ElemAbelianTwo (zpowers V.ki) := elemAbelianTwo_zpowers V.ki_sq'

theorem t_not_mem_ki : t ∉ zpowers V.ki := fun h => V.t_not_mem_zk (mem_sup_right h)

theorem t_comm_ki {a : X} (ha : a ∈ zpowers V.ki) : t * a = a * t := by
  rcases eq_one_or_eq_of_mem_zpowers V.ki_sq' ha with rfl | rfl
  · group
  · exact V.F.kF_comm_t.symm

theorem card_kt : Nat.card (zpowers V.ki ⊔ zpowers t : Subgroup X) = 4 := by
  rw [Sec7.card_sup_of_not_mem V.elemAbelianTwo_ki (SD.t_sq (A := A)) V.t_not_mem_ki
    (fun a ha => V.t_comm_ki ha), Nat.card_zpowers,
    orderOf_eq_prime V.ki_sq' V.ki_ne_one]

theorem exists_C₁ : ∃ c ∈ V.D.C₁, c ∉ (zpowers V.ki ⊔ zpowers t : Subgroup X) := by
  by_contra hne
  push Not at hne
  have hle : V.D.C₁ ⊔ zpowers t ≤ zpowers V.ki ⊔ zpowers t :=
    sup_le (fun c hc => hne c hc) le_sup_right
  rw [V.D.C₁_sup] at hle
  have := Subgroup.card_le_of_le hle
  rw [V.D.card_C, V.card_kt] at this
  norm_num at this

theorem ki_mem_E0' {d : X} (hd : d ∈ zpowers V.ki) : d ∈ S.E0 V.yi V.ki :=
  V.zk_le_E0 (mem_sup_right hd)

theorem option : (V.D.w₂ * V.vN = V.vN * V.D.w₂ ∧ V.w₁N * V.vN = V.vN * V.w₁N) ∨
    (V.D.w₂ * V.vN * V.D.w₂⁻¹ = V.vN * V.yi ∧ V.w₁N * V.vN * V.w₁N⁻¹ = V.vN * S.z) := by
  obtain ⟨c, hc₁, hc⟩ := V.exists_C₁
  have hcC : c ∈ closure ({t, V.ki, V.D.v} : Set X) := V.D.C_eq ▸ V.D.C₁_le hc₁
  have hcomm : ∀ q ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂, c * q = q * c :=
    fun q hq => V.D.C₁_comm c hc₁ q hq
  rcases V.mem_C hcC with h | h
  · exact absurd h hc
  rcases Sec7.mem_or_of_mem_sup V.elemAbelianTwo_ki (SD.t_sq (A := A))
    (fun a ha => V.t_comm_ki ha) h with h' | h'
  · left
    obtain ⟨d, hdE, hcd'⟩ : ∃ d ∈ S.E0 V.yi V.ki, c = d * V.vN :=
      ⟨c * V.vN⁻¹, V.ki_mem_E0' h', by group⟩
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
    refine ⟨key _ V.w₂_mem_Q0 ?_, key _ V.w₁N_mem_Q0 ?_⟩
    · have := V.w₂_conj_E0 hdE
      calc d * V.D.w₂ = V.D.w₂ * (V.D.w₂⁻¹ * d * V.D.w₂) := by group
        _ = V.D.w₂ * d := by
          congr 1
          calc V.D.w₂⁻¹ * d * V.D.w₂ = V.D.w₂⁻¹ * (V.D.w₂ * d * V.D.w₂⁻¹) * V.D.w₂ := by
                rw [this]
            _ = d := by group
    · exact (V.w₁N_comm_E0 hdE).symm
  · right
    obtain ⟨d, hdE, hct⟩ : ∃ d ∈ S.E0 V.yi V.ki, c = d * (t * V.vN) := by
      refine ⟨c * V.vN⁻¹ * t, V.ki_mem_E0' h', ?_⟩
      calc c = c * V.vN⁻¹ * (t * t) * V.vN := by rw [tt (A := A)]; group
        _ = c * V.vN⁻¹ * t * (t * V.vN) := by group
    have key : ∀ q ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂, q * d * q⁻¹ = d →
        q * (t * V.vN) * q⁻¹ = t * V.vN := by
      intro q hq hdq
      have h1 := hcomm q hq
      have h2 : q * c * q⁻¹ = c := by rw [← h1, mul_inv_cancel_right]
      rw [hct, show q * (d * (t * V.vN)) * q⁻¹ = (q * d * q⁻¹) * (q * (t * V.vN) * q⁻¹) by
        group, hdq] at h2
      exact mul_left_cancel h2
    have k1 := key _ V.w₂_mem_Q0 (V.w₂_conj_E0 hdE)
    have k2 := key _ V.w₁N_mem_Q0 (V.w₁N_conj_E0 hdE)
    constructor
    · rw [show V.D.w₂ * (t * V.vN) * V.D.w₂⁻¹ = (V.D.w₂ * t * V.D.w₂⁻¹) *
        (V.D.w₂ * V.vN * V.D.w₂⁻¹) by group, V.w₂_conj_t, mul_assoc] at k1
      have k1' := mul_left_cancel k1
      calc V.D.w₂ * V.vN * V.D.w₂⁻¹ = V.yi * (V.yi * (V.D.w₂ * V.vN * V.D.w₂⁻¹)) := by
            rw [← mul_assoc, V.yi_sq, one_mul]
        _ = V.yi * V.vN := by rw [k1']
        _ = V.vN * V.yi := (V.vN_comm_E0 V.yi_mem_E0).symm
    · rw [show V.w₁N * (t * V.vN) * V.w₁N⁻¹ = (V.w₁N * t * V.w₁N⁻¹) *
        (V.w₁N * V.vN * V.w₁N⁻¹) by group, V.w₁N_conj_t, mul_assoc] at k2
      have k2' := mul_left_cancel k2
      calc V.w₁N * V.vN * V.w₁N⁻¹ = S.z * (S.z * (V.w₁N * V.vN * V.w₁N⁻¹)) := by
            rw [← mul_assoc, zz S, one_mul]
        _ = S.z * V.vN := by rw [k2']
        _ = V.vN * S.z := (V.vN_comm_E0 V.z_mem_E0).symm

theorem C₁_cases : (∃ d ∈ zpowers V.ki, d * V.vN ∈ V.D.C₁) ∨
    (∃ d ∈ zpowers V.ki, d * (t * V.vN) ∈ V.D.C₁) := by
  obtain ⟨c, hc₁, hc⟩ := V.exists_C₁
  have hcC : c ∈ closure ({t, V.ki, V.D.v} : Set X) := V.D.C_eq ▸ V.D.C₁_le hc₁
  rcases V.mem_C hcC with h | h
  · exact absurd h hc
  rcases Sec7.mem_or_of_mem_sup V.elemAbelianTwo_ki (SD.t_sq (A := A))
    (fun a ha => V.t_comm_ki ha) h with h' | h'
  · exact Or.inl ⟨c * V.vN⁻¹, h', by rw [inv_mul_cancel_right]; exact hc₁⟩
  · refine Or.inr ⟨c * V.vN⁻¹ * t, h', ?_⟩
    rw [show c * V.vN⁻¹ * t * (t * V.vN) = c * V.vN⁻¹ * (t * t) * V.vN by group, tt (A := A),
      mul_one, inv_mul_cancel_right]
    exact hc₁

theorem ki_mem_Q0C1 {d : X} (hd : d ∈ zpowers V.ki) :
    d ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ ⊔ V.D.C₁ :=
  mem_sup_left (V.E0_le_Q0 (V.ki_mem_E0' hd))

theorem vN_mem_Q0C1 (h : V.D.w₂ * V.vN = V.vN * V.D.w₂) :
    V.vN ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ ⊔ V.D.C₁ := by
  rcases V.C₁_cases with ⟨d, hd, hc⟩ | ⟨d, hd, hc⟩
  · have : V.vN = d⁻¹ * (d * V.vN) := by group
    rw [this]
    exact mul_mem (V.ki_mem_Q0C1 (inv_mem hd)) (mem_sup_right hc)
  · exfalso
    have hcQ := V.D.C₁_comm _ hc V.D.w₂ V.w₂_mem_Q0
    have hdw : d * V.D.w₂ = V.D.w₂ * d := by
      have := V.w₂_conj_E0 (V.ki_mem_E0' hd)
      calc d * V.D.w₂ = (V.D.w₂ * d * V.D.w₂⁻¹) * V.D.w₂ := by rw [this]
        _ = V.D.w₂ * d := by group
    have h1 : V.D.w₂ * t = t * V.D.w₂ := by
      have e2 : d * (t * (V.vN * V.D.w₂)) = d * (V.D.w₂ * t * V.vN) := by
        calc d * (t * (V.vN * V.D.w₂)) = d * (t * V.vN) * V.D.w₂ := by group
          _ = V.D.w₂ * (d * (t * V.vN)) := hcQ
          _ = (V.D.w₂ * d) * (t * V.vN) := by group
          _ = (d * V.D.w₂) * (t * V.vN) := by rw [hdw]
          _ = d * (V.D.w₂ * t * V.vN) := by group
      have e3 := mul_left_cancel e2
      rw [← h, ← mul_assoc] at e3
      exact (mul_right_cancel e3).symm
    have h2 := V.w₂_conj_t
    rw [h1, mul_inv_cancel_right] at h2
    exact V.F.yF_ne_one (by
      have : V.yi = t⁻¹ * (t * V.yi) := by group
      rw [show V.F.yF = V.yi from rfl, this, ← h2, inv_mul_cancel])

theorem tvN_mem_Q0C1 (h : V.D.w₂ * V.vN * V.D.w₂⁻¹ = V.vN * V.yi) :
    t * V.vN ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ ⊔ V.D.C₁ := by
  rcases V.C₁_cases with ⟨d, hd, hc⟩ | ⟨d, hd, hc⟩
  · exfalso
    have hcQ := V.D.C₁_comm _ hc V.D.w₂ V.w₂_mem_Q0
    have hdw : V.D.w₂ * d * V.D.w₂⁻¹ = d := V.w₂_conj_E0 (V.ki_mem_E0' hd)
    have h1 : V.D.w₂ * (d * V.vN) * V.D.w₂⁻¹ = d * V.vN := by rw [← hcQ, mul_inv_cancel_right]
    rw [show V.D.w₂ * (d * V.vN) * V.D.w₂⁻¹ = (V.D.w₂ * d * V.D.w₂⁻¹) *
      (V.D.w₂ * V.vN * V.D.w₂⁻¹) by group, hdw, h] at h1
    have h3 : V.vN * V.yi = V.vN := mul_left_cancel h1
    exact V.F.yF_ne_one (mul_eq_left.mp h3)
  · have : t * V.vN = d⁻¹ * (d * (t * V.vN)) := by group
    rw [this]
    exact mul_mem (V.ki_mem_Q0C1 (inv_mem hd)) (mem_sup_right hc)

end ISide

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
