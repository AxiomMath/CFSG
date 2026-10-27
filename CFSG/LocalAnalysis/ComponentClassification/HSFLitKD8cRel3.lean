module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cRel2

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace CPair

variable (P : CPair S T₁)

theorem exists_w₂' : ∃ w : X, (w = P.V.D.w₂ ∨ w = P.V.yi * P.V.D.w₂) ∧
    (∃ c ∈ zpowers P.V.ki, w * P.V.D.u * w⁻¹ = c * P.V.yi * P.V.D.w₁ * P.V.D.u) ∧
      w * P.V.D.w₁ * w⁻¹ = P.V.ki * P.V.D.w₁ := by
  obtain ⟨c, hc, hwu⟩ := P.exists_e
  have hκw : P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ = (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ *
      P.V.D.w₁⁻¹) * P.V.D.w₁ := by group
  have hw₂ := P.V.w₂_mul
  have hcw₁ := P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki hc
  have hrel : (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
      (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * (c * (P.V.yi * P.V.ki)) = 1 := by
    have h1 : P.V.D.w₂ * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.D.w₂⁻¹ = P.V.D.u := by
      rw [show P.V.D.w₂ * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.D.w₂⁻¹ =
        (P.V.D.w₂ * P.V.D.w₂) * P.V.D.u * (P.V.D.w₂ * P.V.D.w₂)⁻¹ by group, hw₂, one_mul,
        inv_one, mul_one]
    rw [hwu, show P.V.D.w₂ * (c * P.V.yi * P.V.D.w₁ * P.V.D.u) * P.V.D.w₂⁻¹ =
      (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.yi * P.V.D.w₂⁻¹) *
        (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) by group,
      P.V.w₂_conj_yi, hκw, hwu] at h1
    have h2 : P.V.D.w₁ * (c * P.V.yi) * P.V.D.w₁ = c * (P.V.yi * P.V.ki) := by
      have h3 : P.V.D.w₁ * (c * P.V.yi) * P.V.D.w₁⁻¹ = c * (P.V.yi * P.V.ki) := by
        rw [show P.V.D.w₁ * (c * P.V.yi) * P.V.D.w₁⁻¹ = (P.V.D.w₁ * c * P.V.D.w₁⁻¹) *
          (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹) by group, hcw₁, P.V.w₁_conj_yi]
      rwa [P.V.w₁_inv] at h3
    calc (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
        (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * (c * (P.V.yi * P.V.ki)) =
        (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
          (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * (P.V.D.w₁ * (c * P.V.yi) *
            P.V.D.w₁) := by rw [h2]
      _ = ((P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
          ((P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * P.V.D.w₁) *
            (c * P.V.yi * P.V.D.w₁ * P.V.D.u)) * P.V.D.u⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]
  obtain ⟨φ, e0, e1, e2, e3⟩ := P.V.exists_evE
  have hy : ∀ c' : X, c' * P.V.yi = P.V.yi * c' → P.V.yi * (c' * P.V.yi * P.V.D.w₁ * P.V.D.u) *
      P.V.yi⁻¹ = P.V.yi * c' * P.V.yi * S.z * (P.V.yi * P.V.ki) * P.V.D.w₁ * P.V.D.u := by
    intro c' _
    have hzw := P.V.zk_w₁ P.V.z_mem_zk
    calc P.V.yi * (c' * P.V.yi * P.V.D.w₁ * P.V.D.u) * P.V.yi⁻¹ =
        P.V.yi * c' * P.V.yi * P.V.D.w₁ * (P.V.D.u * P.V.yi) := by rw [P.V.yi_inv]; group
      _ = P.V.yi * c' * P.V.yi * (P.V.D.w₁ * S.z) * (P.V.yi * P.V.D.u) := by
          rw [P.V.u_yi]; group
      _ = P.V.yi * c' * P.V.yi * S.z * (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹) * P.V.D.w₁ *
          P.V.D.u := by rw [← hzw]; group
      _ = _ := by rw [P.V.w₁_conj_yi]
  have hyw : P.V.yi * P.V.D.w₁ * P.V.yi⁻¹ = P.V.ki * P.V.D.w₁ := by
    rw [P.V.yi_w₁, P.V.yi_inv, ← mul_assoc, mul_assoc P.V.D.w₁ P.V.yi,
      ← P.V.ki_comm P.V.yi_mem_TE, mul_assoc P.V.D.w₁, mul_assoc P.V.ki, P.V.yi_sq, mul_one,
      P.V.zk_w₁ P.V.ki_mem_zk]
  have hzy : S.z * P.V.yi = P.V.yi * S.z := central_of_mem_B S Frame.z_mem_B P.V.yi_mem_TE
  have hzky : S.z * P.V.ki * P.V.yi = P.V.yi * (S.z * P.V.ki) :=
    central_of_mem_B S P.zk_mem_B P.V.yi_mem_TE
  rcases P.V.kappa_eq with hκ | hκ <;> rw [hκ] at hrel hκw <;>
    rcases P.w₂_conj_zk_eq (P.V.eq_of_mem_zk hc) with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ |
      ⟨h1, rfl⟩ <;> rw [h1] at hrel
  · exfalso
    have h2 : (1 : X) * P.V.yi * 1 * (1 * (P.V.yi * P.V.ki)) = P.V.ki := by
      elem_eq φ e1 e2 e3 e0
    rw [h2] at hrel
    exact P.V.ki_ne_one hrel
  ·
    refine ⟨P.V.yi * P.V.D.w₂, Or.inr rfl, ⟨P.V.ki, mem_zpowers _, ?_⟩, ?_⟩
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.u * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hwu, hy S.z hzy]
      have h2 : P.V.yi * S.z * P.V.yi * S.z * (P.V.yi * P.V.ki) = P.V.ki * P.V.yi := by
        elem_eq φ e1 e2 e3 e0
      rw [h2]
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.w₁ * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hκw, one_mul, hyw]
  · exfalso
    have h2 : P.V.ki * P.V.yi * 1 * (P.V.ki * (P.V.yi * P.V.ki)) = P.V.ki := by
      elem_eq φ e1 e2 e3 e0
    rw [h2] at hrel
    exact P.V.ki_ne_one hrel
  ·
    refine ⟨P.V.yi * P.V.D.w₂, Or.inr rfl, ⟨1, one_mem _, ?_⟩, ?_⟩
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.u * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hwu,
        hy (S.z * P.V.ki) hzky]
      have h2 : P.V.yi * (S.z * P.V.ki) * P.V.yi * S.z * (P.V.yi * P.V.ki) = 1 * P.V.yi := by
        elem_eq φ e1 e2 e3 e0
      rw [h2]
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.w₁ * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hκw, one_mul, hyw]
  · exact ⟨P.V.D.w₂, Or.inl rfl, ⟨1, one_mem _, hwu⟩, hκw⟩
  · exfalso
    have h2 : S.z * P.V.ki * P.V.yi * P.V.ki * (S.z * (P.V.yi * P.V.ki)) = P.V.ki := by
      elem_eq φ e1 e2 e3 e0
    rw [h2] at hrel
    exact P.V.ki_ne_one hrel
  · exact ⟨P.V.D.w₂, Or.inl rfl, ⟨P.V.ki, mem_zpowers _, hwu⟩, hκw⟩
  · exfalso
    have h2 : S.z * P.V.yi * P.V.ki * (S.z * P.V.ki * (P.V.yi * P.V.ki)) = P.V.ki := by
      elem_eq φ e1 e2 e3 e0
    rw [h2] at hrel
    exact P.V.ki_ne_one hrel

end CPair

end KD8c

end CFSG.ComponentClassification.HSFLit
