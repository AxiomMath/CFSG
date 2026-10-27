module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cPair2

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace CPair

variable (P : CPair S T₁)

theorem w₁_comm_vN : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹ = S.z * P.V.ki := by
  rcases P.V.w₁_comm_C P.V.vN_mem_C with hμ | hμ
  swap
  · exact hμ
  exfalso
  obtain ⟨c, hc, hm⟩ := P.exists_m_eq'
  obtain ⟨b, hb, hn⟩ := P.exists_n_eq
  have hbTE := B_le_TE S hb
  have hcB : c ∈ S.B := P.V.zk_le_B hc
  have hcTE := B_le_TE S hcB
  have hvw : P.V.vN * P.V.D.w₁ * P.V.vN⁻¹ = P.V.D.w₁ := by
    have : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = P.V.vN := by
      calc P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = (P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹) *
          P.V.vN := by group
        _ = P.V.vN := by rw [hμ, one_mul]
    calc P.V.vN * P.V.D.w₁ * P.V.vN⁻¹ =
        (P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹) * P.V.D.w₁ * P.V.vN⁻¹ := by rw [this]
      _ = P.V.D.w₁ := by group
  have hcw : c * P.V.D.w₁ * c⁻¹ = P.V.D.w₁ := by
    have h1 := P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki hc
    calc c * P.V.D.w₁ * c⁻¹ = (P.V.D.w₁ * c * P.V.D.w₁⁻¹) * P.V.D.w₁ * c⁻¹ := by rw [h1]
      _ = P.V.D.w₁ := by group
  have hyw : P.V.yi * P.V.D.w₁ * P.V.yi⁻¹ = P.V.ki * P.V.D.w₁ := by
    have h1 := P.V.w₁_conj_yi
    calc P.V.yi * P.V.D.w₁ * P.V.yi⁻¹ = P.V.yi * (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹)⁻¹ *
          P.V.D.w₁ := by group
      _ = P.V.yi * (P.V.yi * P.V.ki)⁻¹ * P.V.D.w₁ := by rw [h1]
      _ = P.V.ki * P.V.D.w₁ := by
          rw [mul_inv_rev, P.V.ki_inv, P.V.yi_inv, ← mul_assoc,
            ← P.V.ki_comm P.V.yi_mem_TE, mul_assoc P.V.ki, P.V.yi_sq, mul_one]
  have hyx : P.V.yi * (S.x * P.V.yi * b) * P.V.yi⁻¹ = S.z * (S.x * P.V.yi) * b := by
    have hinv := P.V.hyi.inv
    rw [x_inv_eq S] at hinv
    calc P.V.yi * (S.x * P.V.yi * b) * P.V.yi⁻¹ = (P.V.yi * S.x * P.V.yi⁻¹) * P.V.yi *
        (P.V.yi * b * P.V.yi⁻¹) := by group
      _ = S.z * (S.x * P.V.yi) * b := by
          rw [hinv, show P.V.yi * b * P.V.yi⁻¹ = b by
            rw [← central_of_mem_B S hb P.V.yi_mem_TE, mul_inv_cancel_right], mul_assoc S.z]
  have hcx : c * (S.x * P.V.yi * b) * c⁻¹ = S.x * P.V.yi * b := by
    rw [central_of_mem_B S hcB (mul_mem P.V.xyi_mem_TE hbTE), mul_inv_cancel_right]
  have hmn : P.W.D.w₁ * P.W.D.v * P.W.D.w₁⁻¹ * P.W.D.v⁻¹ = 1 ∨
      P.W.D.w₁ * P.W.D.v * P.W.D.w₁⁻¹ * P.W.D.v⁻¹ = P.V.ki := by
    rcases P.W.w₁_comm_C P.W.v_mem_C with h | h
    · exact Or.inl h
    · right; rw [h, P.hkk, ← mul_assoc, zz S, one_mul]
  have hb'B : P.V.vN * b * P.V.vN⁻¹ ∈ S.B := by
    rcases P.V.vN_conj_B hb with h | h <;> rw [h]
    · exact hb
    · exact mul_mem hb P.V.ki_mem_B
  set b' := P.V.vN * b * P.V.vN⁻¹ with hb'
  have hcomm : P.W.D.w₁ * P.W.D.v * P.W.D.w₁⁻¹ * P.W.D.v⁻¹ = S.z * (b' * b⁻¹) := by
    rw [hm, hn]
    have e1 : P.V.vN * P.V.yi * c * (P.V.D.w₁ * (S.x * P.V.yi) * b) *
        (P.V.vN * P.V.yi * c)⁻¹ = P.V.vN * ((P.V.yi * c) * P.V.D.w₁ * (P.V.yi * c)⁻¹) *
          ((P.V.yi * c) * (S.x * P.V.yi * b) * (P.V.yi * c)⁻¹) * P.V.vN⁻¹ := by group
    have e2 : (P.V.yi * c) * P.V.D.w₁ * (P.V.yi * c)⁻¹ = P.V.ki * P.V.D.w₁ := by
      rw [show (P.V.yi * c) * P.V.D.w₁ * (P.V.yi * c)⁻¹ = P.V.yi * (c * P.V.D.w₁ * c⁻¹) *
        P.V.yi⁻¹ by group, hcw, hyw]
    have e3 : (P.V.yi * c) * (S.x * P.V.yi * b) * (P.V.yi * c)⁻¹ =
        S.z * (S.x * P.V.yi) * b := by
      rw [show (P.V.yi * c) * (S.x * P.V.yi * b) * (P.V.yi * c)⁻¹ =
        P.V.yi * (c * (S.x * P.V.yi * b) * c⁻¹) * P.V.yi⁻¹ by group, hcx, hyx]
    have e4 : P.V.vN * (P.V.ki * P.V.D.w₁ * (S.z * (S.x * P.V.yi) * b)) * P.V.vN⁻¹ =
        P.V.ki * P.V.D.w₁ * (S.z * (P.V.ki * (S.x * P.V.yi)) * b') := by
      rw [show P.V.vN * (P.V.ki * P.V.D.w₁ * (S.z * (S.x * P.V.yi) * b)) * P.V.vN⁻¹ =
        (P.V.vN * P.V.ki * P.V.vN⁻¹) * (P.V.vN * P.V.D.w₁ * P.V.vN⁻¹) *
          ((P.V.vN * S.z * P.V.vN⁻¹) * (P.V.vN * (S.x * P.V.yi) * P.V.vN⁻¹) * b') by
        rw [hb']; group, P.V.vN_conj_ki, hvw, P.V.vN_conj_z, P.vN_conj_xyi]
    rw [show P.V.vN * P.V.yi * c * (P.V.D.w₁ * (S.x * P.V.yi) * b) *
      (P.V.vN * P.V.yi * c)⁻¹ * (P.V.D.w₁ * (S.x * P.V.yi) * b)⁻¹ =
        (P.V.vN * P.V.yi * c * (P.V.D.w₁ * (S.x * P.V.yi) * b) * (P.V.vN * P.V.yi * c)⁻¹) *
          (P.V.D.w₁ * (S.x * P.V.yi) * b)⁻¹ by group, e1, e2, e3,
      show P.V.vN * (P.V.ki * P.V.D.w₁) * (S.z * (S.x * P.V.yi) * b) * P.V.vN⁻¹ =
        P.V.vN * (P.V.ki * P.V.D.w₁ * (S.z * (S.x * P.V.yi) * b)) * P.V.vN⁻¹ by group, e4]
    have hd : b' * b⁻¹ ∈ S.B := mul_mem hb'B (inv_mem hb)
    have hdzk : S.z * (b' * b⁻¹) ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X) := by
      refine mul_mem P.V.z_mem_zk ?_
      rcases P.V.vN_conj_B hb with h | h <;> rw [← hb'] at h <;> rw [h]
      · rw [mul_inv_cancel]; exact one_mem _
      · rw [mul_assoc, P.V.ki_comm (inv_mem hbTE), ← mul_assoc, mul_inv_cancel, one_mul]
        exact P.V.ki_mem_zk
    have hfix := P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki hdzk
    calc P.V.ki * P.V.D.w₁ * (S.z * (P.V.ki * (S.x * P.V.yi)) * b') *
        (P.V.D.w₁ * (S.x * P.V.yi) * b)⁻¹ =
        P.V.ki * P.V.D.w₁ * (S.z * P.V.ki * ((S.x * P.V.yi) * (b' * b⁻¹) *
          (S.x * P.V.yi)⁻¹)) * P.V.D.w₁⁻¹ := by group
      _ = P.V.ki * P.V.D.w₁ * (P.V.ki * (S.z * (b' * b⁻¹))) * P.V.D.w₁⁻¹ := by
          rw [← central_of_mem_B S hd P.V.xyi_mem_TE, mul_inv_cancel_right,
            ← P.V.ki_comm (R_le_TE S (z_mem_R S)), mul_assoc P.V.ki S.z]
      _ = P.V.ki * (P.V.D.w₁ * P.V.ki * P.V.D.w₁⁻¹) * (P.V.D.w₁ * (S.z * (b' * b⁻¹)) *
          P.V.D.w₁⁻¹) := by group
      _ = S.z * (b' * b⁻¹) := by rw [P.V.w₁_conj_ki, hfix, ← mul_assoc, P.V.ki_sq, one_mul]
  rw [hcomm] at hmn
  rcases P.V.vN_conj_B hb with h | h <;> rw [← hb'] at h <;> rw [h] at hmn
  · rw [mul_inv_cancel, mul_one] at hmn
    rcases hmn with h1 | h1
    · exact z_ne_one S h1
    · exact P.V.ki_ne_z h1.symm
  · have e : b * P.V.ki * b⁻¹ = P.V.ki := by
      rw [← P.V.ki_comm hbTE, mul_inv_cancel_right]
    rw [e] at hmn
    rcases hmn with h1 | h1
    · apply P.V.ki_ne_z
      calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, zz S, one_mul]
        _ = S.z := by rw [h1, mul_one]
    · exact z_ne_one S (mul_eq_right.mp h1)

theorem w₁_conj_vN : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = P.V.vN * (S.z * P.V.ki) := by
  have h := P.w₁_comm_vN
  have hc : P.V.vN * (S.z * P.V.ki) * P.V.vN⁻¹ = S.z * P.V.ki :=
    P.V.vN_conj_of_zk (mul_mem P.V.z_mem_zk P.V.ki_mem_zk)
  calc P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ = (P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹) *
        P.V.vN := by group
    _ = (P.V.vN * (S.z * P.V.ki) * P.V.vN⁻¹) * P.V.vN := by rw [h, hc]
    _ = P.V.vN * (S.z * P.V.ki) := by group

end CPair

end KD8c

end CFSG.ComponentClassification.HSFLit
