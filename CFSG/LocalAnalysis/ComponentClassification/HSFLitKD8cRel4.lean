module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cRel3
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MC

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem B_le_E' (S : KDBase A C) (yi : X) : S.B ≤ S.E yi := by
  refine closure_mono ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  tauto

namespace VSide

variable (V : VSide S T₁)

theorem conj_E {e f : X} (he : e ∈ S.E V.yi) (hf : f ∈ S.E V.yi) : e * f * e⁻¹ = f := by
  rw [V.E_comm he hf, mul_inv_cancel_right]

end VSide

namespace CPair

variable (P : CPair S T₁)

noncomputable def w₂N : X := Classical.choose P.exists_w₂'

theorem w₂N_eq : P.w₂N = P.V.D.w₂ ∨ P.w₂N = P.V.yi * P.V.D.w₂ :=
  (Classical.choose_spec P.exists_w₂').1

theorem exists_c : ∃ c ∈ zpowers P.V.ki,
    P.w₂N * P.V.D.u * P.w₂N⁻¹ = c * P.V.yi * P.V.D.w₁ * P.V.D.u :=
  (Classical.choose_spec P.exists_w₂').2.1

theorem w₂N_conj_w₁ : P.w₂N * P.V.D.w₁ * P.w₂N⁻¹ = P.V.ki * P.V.D.w₁ :=
  (Classical.choose_spec P.exists_w₂').2.2

noncomputable def cN : X := Classical.choose P.exists_c

theorem cN_mem : P.cN ∈ zpowers P.V.ki := (Classical.choose_spec P.exists_c).1

theorem w₂N_conj_u' : P.w₂N * P.V.D.u * P.w₂N⁻¹ = P.cN * P.V.yi * P.V.D.w₁ * P.V.D.u :=
  (Classical.choose_spec P.exists_c).2

@[expose] noncomputable def w₁N : X := P.V.D.w₁ * P.cN

theorem w₁N_eq : P.w₁N = P.V.D.w₁ * P.cN := rfl

theorem cN_eq : P.cN = 1 ∨ P.cN = P.V.ki := P.V.eq_of_mem_ki P.cN_mem

theorem cN_mem_zk : P.cN ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X) :=
  mem_sup_right P.cN_mem

theorem cN_mem_B : P.cN ∈ S.B := P.V.zk_le_B P.cN_mem_zk

theorem cN_mem_E : P.cN ∈ S.E P.V.yi := B_le_E' S _ P.cN_mem_B

theorem cN_comm_w₁ : P.cN * P.V.D.w₁ = P.V.D.w₁ * P.cN := P.V.zk_w₁ P.cN_mem_zk

theorem w₁N_conj_E {e : X} (he : e ∈ S.E P.V.yi) :
    P.w₁N * e * P.w₁N⁻¹ = P.V.D.w₁ * e * P.V.D.w₁⁻¹ := by
  rw [P.w₁N_eq, show P.V.D.w₁ * P.cN * e * (P.V.D.w₁ * P.cN)⁻¹ =
    P.V.D.w₁ * (P.cN * e * P.cN⁻¹) * P.V.D.w₁⁻¹ by group, P.V.conj_E P.cN_mem_E he]

theorem w₁N_sq : P.w₁N * P.w₁N = 1 := by
  have hw := P.V.w₁_mul
  rw [P.w₁N_eq, show P.V.D.w₁ * P.cN * (P.V.D.w₁ * P.cN) = P.cN * P.V.D.w₁ * P.V.D.w₁ * P.cN by
    rw [P.cN_comm_w₁]; group, mul_assoc P.cN, hw, mul_one, ← pow_two,
    sq_of_mem_B S P.cN_mem_B]

theorem w₁N_conj_z : P.w₁N * S.z * P.w₁N⁻¹ = S.z := by
  rw [P.w₁N_conj_E (Frame.z_mem_E _), P.V.w₁_conj_z]

theorem w₁N_conj_yi : P.w₁N * P.V.yi * P.w₁N⁻¹ = P.V.yi * P.V.ki := by
  rw [P.w₁N_conj_E (Frame.yi_mem_E _), P.V.w₁_conj_yi]

theorem w₁N_conj_t : P.w₁N * t * P.w₁N⁻¹ = S.z * (t * P.V.ki) := by
  rw [P.w₁N_conj_E (Frame.t_mem_E _), P.V.w₁_conj_t, ← B_comm_B S Frame.z_mem_B Frame.t_mem_B,
    mul_assoc]

theorem w₁N_conj_ki : P.w₁N * P.V.ki * P.w₁N⁻¹ = P.V.ki := by
  rw [P.w₁N_conj_E P.V.ki_mem_E, P.V.w₁_conj_ki]

theorem w₁N_conj_vN : P.w₁N * P.V.vN * P.w₁N⁻¹ = P.V.vN * (S.z * P.V.ki) := by
  have hc : P.cN * P.V.vN * P.cN⁻¹ = P.V.vN := by
    have h := P.V.vN_conj_of_zk P.cN_mem_zk
    have h' : P.V.vN * P.cN = P.cN * P.V.vN := by
      calc P.V.vN * P.cN = (P.V.vN * P.cN * P.V.vN⁻¹) * P.V.vN := by group
        _ = P.cN * P.V.vN := by rw [h]
    rw [← h', mul_inv_cancel_right]
  rw [P.w₁N_eq, show P.V.D.w₁ * P.cN * P.V.vN * (P.V.D.w₁ * P.cN)⁻¹ =
    P.V.D.w₁ * (P.cN * P.V.vN * P.cN⁻¹) * P.V.D.w₁⁻¹ by group, hc, P.w₁_conj_vN]

theorem u_conj_w₁N : P.V.D.u * P.w₁N * P.V.D.u⁻¹ = P.w₁N * (S.z * P.V.ki) := by
  rw [P.w₁N_eq, show P.V.D.u * (P.V.D.w₁ * P.cN) * P.V.D.u⁻¹ = (P.V.D.u * P.V.D.w₁ * P.V.D.u⁻¹) *
    (P.V.D.u * P.cN * P.V.D.u⁻¹) by group, P.u_conj_w₁, P.V.u_conj_B P.cN_mem_B, mul_assoc,
    P.zk_comm (B_le_TE S P.cN_mem_B), ← mul_assoc]

theorem w₂N_conj_E {e : X} (he' : P.V.D.w₂ * e * P.V.D.w₂⁻¹ ∈ S.E P.V.yi) :
    P.w₂N * e * P.w₂N⁻¹ = P.V.D.w₂ * e * P.V.D.w₂⁻¹ := by
  rcases P.w₂N_eq with h | h <;> rw [h]
  rw [show P.V.yi * P.V.D.w₂ * e * (P.V.yi * P.V.D.w₂)⁻¹ =
    P.V.yi * (P.V.D.w₂ * e * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group,
    P.V.conj_E (Frame.yi_mem_E _) he']

theorem w₂N_sq : P.w₂N * P.w₂N = 1 := by
  have hw := P.V.w₂_mul
  rcases P.w₂N_eq with h | h <;> rw [h]
  · exact hw
  · rw [show P.V.yi * P.V.D.w₂ * (P.V.yi * P.V.D.w₂) =
      P.V.yi * (P.V.D.w₂ * P.V.yi * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.D.w₂) by group, hw, mul_one,
      P.V.w₂_conj_yi, P.V.yi_sq]

theorem w₂N_conj_z : P.w₂N * S.z * P.w₂N⁻¹ = S.z * P.V.ki := by
  have h : P.V.D.w₂ * S.z * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_z]; exact mul_mem (Frame.z_mem_E _) P.V.ki_mem_E
  rw [P.w₂N_conj_E h, P.V.w₂_conj_z]

theorem w₂N_conj_yi : P.w₂N * P.V.yi * P.w₂N⁻¹ = P.V.yi := by
  have h : P.V.D.w₂ * P.V.yi * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_yi]; exact Frame.yi_mem_E _
  rw [P.w₂N_conj_E h, P.V.w₂_conj_yi]

theorem w₂N_conj_t : P.w₂N * t * P.w₂N⁻¹ = P.V.yi * (t * P.V.ki) := by
  have h : P.V.D.w₂ * t * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_t]
    exact mul_mem (mul_mem (Frame.t_mem_E _) (Frame.yi_mem_E _)) P.V.ki_mem_E
  rw [P.w₂N_conj_E h, P.V.w₂_conj_t, P.V.E_comm (Frame.t_mem_E _) (Frame.yi_mem_E _), mul_assoc]

theorem w₂N_conj_ki : P.w₂N * P.V.ki * P.w₂N⁻¹ = P.V.ki := by
  have h : P.V.D.w₂ * P.V.ki * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_ki]; exact P.V.ki_mem_E
  rw [P.w₂N_conj_E h, P.V.w₂_conj_ki]

theorem w₂N_conj_vN : P.w₂N * P.V.vN * P.w₂N⁻¹ = P.V.vN * (P.V.yi * P.V.ki) := by
  rcases P.w₂N_eq with h | h <;> rw [h]
  · exact P.w₂_conj_vN
  · have hyv : P.V.yi * P.V.vN = P.V.vN * P.V.yi := by
      calc P.V.yi * P.V.vN = (P.V.vN * P.V.yi * P.V.vN⁻¹) * P.V.vN := by rw [P.V.vN_conj_yi]
        _ = P.V.vN * P.V.yi := by group
    have hyk : P.V.yi * (P.V.yi * P.V.ki) * P.V.yi⁻¹ = P.V.yi * P.V.ki :=
      P.V.conj_E (Frame.yi_mem_E _) (mul_mem (Frame.yi_mem_E _) P.V.ki_mem_E)
    calc P.V.yi * P.V.D.w₂ * P.V.vN * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹) * P.V.yi⁻¹ := by group
      _ = (P.V.yi * P.V.vN) * (P.V.yi * P.V.ki) * P.V.yi⁻¹ := by rw [P.w₂_conj_vN]; group
      _ = P.V.vN * (P.V.yi * (P.V.yi * P.V.ki) * P.V.yi⁻¹) := by rw [hyv]; group
      _ = P.V.vN * (P.V.yi * P.V.ki) := by rw [hyk]

theorem w₂N_conj_w₁N : P.w₂N * P.w₁N * P.w₂N⁻¹ = P.w₁N * P.V.ki := by
  have hc : P.w₂N * P.cN * P.w₂N⁻¹ = P.cN := by
    rcases P.cN_eq with h | h <;> rw [h]
    · group
    · exact P.w₂N_conj_ki
  rw [P.w₁N_eq]
  calc P.w₂N * (P.V.D.w₁ * P.cN) * P.w₂N⁻¹ = (P.w₂N * P.V.D.w₁ * P.w₂N⁻¹) *
      (P.w₂N * P.cN * P.w₂N⁻¹) := by group
    _ = (P.V.ki * P.V.D.w₁) * P.cN := by rw [P.w₂N_conj_w₁, hc]
    _ = P.V.D.w₁ * (P.V.ki * P.cN) := by rw [P.V.zk_w₁ P.V.ki_mem_zk]; group
    _ = P.V.D.w₁ * P.cN * P.V.ki := by rw [P.V.ki_comm (B_le_TE S P.cN_mem_B)]; group

theorem w₂N_conj_u : P.w₂N * P.V.D.u * P.w₂N⁻¹ = P.V.D.u * (P.w₁N * P.V.yi) := by
  rw [P.w₂N_conj_u', P.w₁N_eq]
  obtain ⟨φ, e0, e1, e2, e3⟩ := P.V.exists_evE
  have hB : P.cN * P.V.D.u = P.V.D.u * P.cN := P.V.B_u P.cN_mem_B
  calc P.cN * P.V.yi * P.V.D.w₁ * P.V.D.u = P.cN * (P.V.yi * P.V.D.w₁) * P.V.D.u := by group
    _ = P.cN * (P.V.D.w₁ * (P.V.yi * P.V.ki)) * P.V.D.u := by rw [P.V.yi_w₁]
    _ = (P.cN * P.V.D.w₁) * (P.V.yi * P.V.ki) * P.V.D.u := by group
    _ = P.V.D.w₁ * (P.cN * (P.V.yi * P.V.ki)) * P.V.D.u := by rw [P.cN_comm_w₁]; group
    _ = P.V.D.w₁ * (S.z * P.V.ki * P.cN * (S.z * P.V.yi)) * P.V.D.u := by
        congr 2
        rcases P.cN_eq with h | h <;> rw [h] <;> elem_eq φ e1 e2 e3 e0
    _ = P.V.D.w₁ * (S.z * P.V.ki) * P.cN * (S.z * P.V.yi * P.V.D.u) := by group
    _ = P.V.D.w₁ * (S.z * P.V.ki) * (P.cN * P.V.D.u) * P.V.yi := by rw [← P.V.u_yi]; group
    _ = (P.V.D.w₁ * (S.z * P.V.ki) * P.V.D.u) * P.cN * P.V.yi := by rw [hB]; group
    _ = P.V.D.u * (P.V.D.w₁ * P.cN * P.V.yi) := by rw [← P.u_w₁]; group

theorem pcX : MC.PcX P.w₂N P.V.D.u P.w₁N P.V.vN S.z P.V.yi t P.V.ki where
  w₂_sq := P.w₂N_sq
  w₂_u := P.w₂N_conj_u
  w₂_w₁ := P.w₂N_conj_w₁N
  w₂_v := P.w₂N_conj_vN
  w₂_z := P.w₂N_conj_z
  w₂_y := P.w₂N_conj_yi
  w₂_t := P.w₂N_conj_t
  w₂_k := P.w₂N_conj_ki
  u_sq := P.V.u_sq
  u_w₁ := P.u_conj_w₁N
  u_v := P.V.u_conj_vN
  u_z := P.V.u_conj_z
  u_y := P.V.u_conj_yi
  u_t := P.V.u_conj_t
  u_k := P.V.u_conj_ki
  w₁_sq := P.w₁N_sq
  w₁_v := P.w₁N_conj_vN
  w₁_z := P.w₁N_conj_z
  w₁_y := P.w₁N_conj_yi
  w₁_t := P.w₁N_conj_t
  w₁_k := P.w₁N_conj_ki
  v_sq := P.V.vN_mul_vN
  v_z := P.V.vN_conj_z
  v_y := P.V.vN_conj_yi
  v_t := P.V.vN_conj_t
  v_k := P.V.vN_conj_ki
  z_sq := zz S
  z_y := P.V.conj_E (Frame.z_mem_E _) (Frame.yi_mem_E _)
  z_t := P.V.conj_E (Frame.z_mem_E _) (Frame.t_mem_E _)
  z_k := P.V.conj_E (Frame.z_mem_E _) P.V.ki_mem_E
  y_sq := P.V.yi_sq
  y_t := P.V.conj_E (Frame.yi_mem_E _) (Frame.t_mem_E _)
  y_k := P.V.conj_E (Frame.yi_mem_E _) P.V.ki_mem_E
  t_sq := tt (A := A)
  t_k := P.V.conj_E (Frame.t_mem_E _) P.V.ki_mem_E
  k_sq := P.V.ki_sq

end CPair

end KD8c

end CFSG.ComponentClassification.HSFLit
