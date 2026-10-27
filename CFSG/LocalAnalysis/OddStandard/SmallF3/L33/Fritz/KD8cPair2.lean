module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cPair

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace CPair

variable (P : CPair S T₁)

theorem m_conj_t : P.W.D.w₁ * t * P.W.D.w₁⁻¹ = t * P.V.ki := by
  rw [P.W.w₁_conj_t, P.hkk, mul_assoc, ← mul_assoc S.z, zz S, one_mul]

theorem vN_conj_k : P.V.vN * S.k * P.V.vN⁻¹ = S.k := P.V.vN_conj_of_zk P.V.k_mem_zk

theorem rho_mem_TE : P.V.vN⁻¹ * P.W.D.w₁ ∈ S.TE := by
  have hv := P.V.vN_inv
  refine mem_TE_of_mem_T₁ S P.V.h4 (mul_mem (inv_mem P.V.vN_mem_T₁) P.W.w₁_mem_T₁) ?_ ?_
  · have h1 : (P.V.vN⁻¹ * P.W.D.w₁) * t * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ = t := by
      calc (P.V.vN⁻¹ * P.W.D.w₁) * t * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ =
          P.V.vN⁻¹ * (P.W.D.w₁ * t * P.W.D.w₁⁻¹) * P.V.vN := by group
        _ = P.V.vN⁻¹ * (P.V.vN * t * P.V.vN⁻¹) * P.V.vN := by rw [P.m_conj_t, P.V.vN_conj_t]
        _ = t := by group
    calc (P.V.vN⁻¹ * P.W.D.w₁) * t = (P.V.vN⁻¹ * P.W.D.w₁) * t *
        (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ * (P.V.vN⁻¹ * P.W.D.w₁) := by group
      _ = t * (P.V.vN⁻¹ * P.W.D.w₁) := by rw [h1]
  · have h1 : (P.V.vN⁻¹ * P.W.D.w₁) * S.k * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ = S.k := by
      calc (P.V.vN⁻¹ * P.W.D.w₁) * S.k * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ =
          P.V.vN⁻¹ * (P.W.D.w₁ * S.k * P.W.D.w₁⁻¹) * P.V.vN := by group
        _ = P.V.vN * S.k * P.V.vN⁻¹ := by rw [P.W.w₁_conj_k, hv]
        _ = S.k := P.vN_conj_k
    calc (P.V.vN⁻¹ * P.W.D.w₁) * S.k = (P.V.vN⁻¹ * P.W.D.w₁) * S.k *
        (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ * (P.V.vN⁻¹ * P.W.D.w₁) := by group
      _ = S.k * (P.V.vN⁻¹ * P.W.D.w₁) := by rw [h1]

theorem vN_conj_xyi : P.V.vN * (S.x * P.V.yi) * P.V.vN⁻¹ = P.V.ki * (S.x * P.V.yi) := by
  rw [show P.V.vN * (S.x * P.V.yi) * P.V.vN⁻¹ = (P.V.vN * S.x * P.V.vN⁻¹) *
    (P.V.vN * P.V.yi * P.V.vN⁻¹) by group, P.V.vN_conj_x, P.V.vN_conj_yi, mul_assoc]

theorem vN_conj_yW : P.V.vN * P.W.yi * P.V.vN⁻¹ = P.V.ki * P.W.yi := by
  rw [P.hyy]; exact P.vN_conj_xyi

theorem rho_conj_yW : (P.V.vN⁻¹ * P.W.D.w₁) * P.W.yi * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ =
    S.z * P.W.yi := by
  have hv := P.V.vN_inv
  have h1 : P.V.vN⁻¹ * P.W.yi * P.V.vN = P.V.ki * P.W.yi := by
    rw [hv]; nth_rewrite 2 [← hv]; exact P.vN_conj_yW
  have hzk : P.V.vN⁻¹ * (S.z * P.V.ki) * P.V.vN = S.z * P.V.ki := by
    rw [hv]; nth_rewrite 2 [← hv]
    exact P.V.vN_conj_of_zk (mul_mem P.V.z_mem_zk P.V.ki_mem_zk)
  have hw := P.W.w₁_conj_yi
  calc (P.V.vN⁻¹ * P.W.D.w₁) * P.W.yi * (P.V.vN⁻¹ * P.W.D.w₁)⁻¹ =
      P.V.vN⁻¹ * (P.W.D.w₁ * P.W.yi * P.W.D.w₁⁻¹) * P.V.vN := by group
    _ = (P.V.vN⁻¹ * P.W.yi * P.V.vN) * (P.V.vN⁻¹ * (S.z * P.V.ki) * P.V.vN) := by
        rw [hw, P.hkk]; group
    _ = P.V.ki * P.W.yi * (S.z * P.V.ki) := by rw [h1, hzk]
    _ = P.W.yi * (S.z * (P.V.ki * P.V.ki)) := by
        rw [P.V.ki_comm P.W.yi_mem_TE, mul_assoc, ← mul_assoc P.V.ki,
          P.V.ki_comm (R_le_TE S (z_mem_R S)), mul_assoc]
    _ = S.z * P.W.yi := by
        rw [P.V.ki_sq, mul_one, ← central_of_mem_B S Frame.z_mem_B P.W.yi_mem_TE]

theorem rho_not_mem_xB : S.x⁻¹ * (P.V.vN⁻¹ * P.W.D.w₁) ∉ S.B := by
  intro hb0
  obtain ⟨b, hb, hm⟩ : ∃ b ∈ S.B, P.W.D.w₁ = P.V.vN * (S.x * b) := ⟨_, hb0, by group⟩
  have hbTE := B_le_TE S hb
  have hvv := P.V.vN_mul_vN
  have hsq := P.W.w₁_mul
  rw [hm] at hsq
  have hb'B : P.V.vN * b * P.V.vN⁻¹ ∈ S.B := by
    rcases P.V.vN_conj_B hb with h | h <;> rw [h]
    · exact hb
    · exact mul_mem hb P.V.ki_mem_B
  set b' := P.V.vN * b * P.V.vN⁻¹ with hb'
  have e : P.V.vN * (S.x * b) * (P.V.vN * (S.x * b)) = S.z * P.V.ki * (b' * b) := by
    calc P.V.vN * (S.x * b) * (P.V.vN * (S.x * b)) =
        (P.V.vN * S.x * P.V.vN⁻¹) * b' * (P.V.vN * P.V.vN) * (S.x * b) := by
          rw [hb']; group
      _ = P.V.ki * (S.x * b' * S.x) * b := by
          rw [P.V.vN_conj_x, hvv, mul_one]; group
      _ = P.V.ki * ((S.x * S.x) * b') * b := by
          rw [mul_assoc S.x, central_of_mem_B S hb'B (R_le_TE S S.x_mem)]; group
      _ = S.z * P.V.ki * (b' * b) := by
          rw [xx S, ← P.V.ki_comm (R_le_TE S (z_mem_R S))]; group
  rw [e] at hsq
  have hbb : b * b = 1 := by rw [← pow_two, sq_of_mem_B S hb]
  rcases P.V.vN_conj_B hb with h | h <;> rw [← hb'] at h <;> rw [h] at hsq
  · rw [hbb, mul_one] at hsq
    apply P.V.ki_ne_z
    calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, zz S, one_mul]
      _ = S.z := by rw [hsq, mul_one]
  · rw [mul_assoc b, P.V.ki_comm hbTE, ← mul_assoc b, hbb, one_mul, mul_assoc, P.V.ki_sq,
      mul_one] at hsq
    exact z_ne_one S hsq

theorem exists_m_eq : ∃ c ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X),
    P.W.D.w₁ = P.V.vN * (S.x * P.W.yi) * c := by
  have hb := (mem_xB_of_conj_refl P.W.hyi P.rho_mem_TE P.rho_conj_yW).resolve_left
    P.rho_not_mem_xB
  obtain ⟨b, hb, hm⟩ : ∃ b ∈ S.B, P.W.D.w₁ = P.V.vN * (S.x * P.W.yi) * b :=
    ⟨_, hb, by group⟩
  refine ⟨b, ?_, hm⟩
  have hvv := P.V.vN_mul_vN
  have hsq := P.W.w₁_mul
  rw [hm] at hsq
  have hxy := P.W.xyi_sq
  have hbTE := B_le_TE S hb
  have hxyTE : S.x * P.W.yi ∈ S.TE := P.W.xyi_mem_TE
  have h1 : P.V.vN * (S.x * P.W.yi) * P.V.vN⁻¹ = S.x * P.W.yi := by
    rw [show P.V.vN * (S.x * P.W.yi) * P.V.vN⁻¹ = (P.V.vN * S.x * P.V.vN⁻¹) *
      (P.V.vN * P.W.yi * P.V.vN⁻¹) by group, P.V.vN_conj_x, P.vN_conj_yW,
      show P.V.ki * S.x * (P.V.ki * P.W.yi) = S.x * (P.V.ki * P.V.ki) * P.W.yi by
        rw [P.V.ki_comm (R_le_TE S S.x_mem)]; group, P.V.ki_sq, mul_one]
  have hb'B : P.V.vN * b * P.V.vN⁻¹ ∈ S.B := by
    rcases P.V.vN_conj_B hb with h | h <;> rw [h]
    · exact hb
    · exact mul_mem hb P.V.ki_mem_B
  have e : P.V.vN * (S.x * P.W.yi) * b * (P.V.vN * (S.x * P.W.yi) * b) =
      (P.V.vN * b * P.V.vN⁻¹) * b := by
    calc P.V.vN * (S.x * P.W.yi) * b * (P.V.vN * (S.x * P.W.yi) * b) =
        (P.V.vN * (S.x * P.W.yi) * P.V.vN⁻¹) * (P.V.vN * b * P.V.vN⁻¹) * (P.V.vN * P.V.vN) *
          ((S.x * P.W.yi) * b) := by group
      _ = (S.x * P.W.yi) * (P.V.vN * b * P.V.vN⁻¹) * ((S.x * P.W.yi) * b) := by
          rw [h1, hvv, mul_one]
      _ = (P.V.vN * b * P.V.vN⁻¹) * ((S.x * P.W.yi) * (S.x * P.W.yi)) * b := by
          rw [← central_of_mem_B S hb'B hxyTE]; group
      _ = (P.V.vN * b * P.V.vN⁻¹) * b := by rw [hxy, mul_one]
  rw [e] at hsq
  rcases P.V.mem_B_cases hb with h | h
  · exact h
  · exfalso
    rw [P.V.vN_conj_of_t h] at hsq
    have hbb : b * b = 1 := by rw [← pow_two, sq_of_mem_B S hb]
    rw [mul_assoc, P.V.ki_comm hbTE, ← mul_assoc, hbb, one_mul] at hsq
    exact P.V.ki_ne_one hsq

theorem exists_m_eq' : ∃ c ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X),
    P.W.D.w₁ = P.V.vN * P.V.yi * c := by
  obtain ⟨c, hc, hm⟩ := P.exists_m_eq
  rw [P.x_mul_yW] at hm
  refine ⟨S.z * c, mul_mem P.V.z_mem_zk hc, ?_⟩
  rw [hm, central_of_mem_B S Frame.z_mem_B P.V.yi_mem_TE]; group

end CPair

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
