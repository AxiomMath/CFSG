module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cRel

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace CPair

variable (P : CPair S T₁)

theorem u_w₁ : P.V.D.u * P.V.D.w₁ = P.V.D.w₁ * (S.z * P.V.ki) * P.V.D.u := by
  rw [← P.u_conj_w₁]; group

theorem wu_not_mem_E0 : P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * P.V.D.u⁻¹ ∉ S.E0 P.V.yi P.V.ki := by
  intro h
  set c := P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * P.V.D.u⁻¹ with hc
  have hwu : P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ = c * P.V.D.u := by rw [hc]; group
  have hcE : c ∈ S.E P.V.yi := P.V.E0_le_E h
  have h1 : (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * (P.V.D.w₂ * t * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹)⁻¹ = P.V.D.w₂ * t * P.V.D.w₂⁻¹ := by
    rw [show (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * (P.V.D.w₂ * t * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹)⁻¹ = P.V.D.w₂ * (P.V.D.u * t * P.V.D.u⁻¹) *
        P.V.D.w₂⁻¹ by group, P.V.u_conj_t]
  rw [hwu, P.V.w₂_conj_t] at h1
  have hmem : t * (S.z * P.V.yi) * P.V.ki ∈ S.E P.V.yi :=
    mul_mem (mul_mem (Frame.t_mem_E _) (mul_mem (Frame.z_mem_E _) (Frame.yi_mem_E _)))
      P.V.ki_mem_E
  have h2 : c * P.V.D.u * (t * P.V.yi * P.V.ki) * (c * P.V.D.u)⁻¹ =
      t * (S.z * P.V.yi) * P.V.ki := by
    rw [show c * P.V.D.u * (t * P.V.yi * P.V.ki) * (c * P.V.D.u)⁻¹ =
      c * ((P.V.D.u * t * P.V.D.u⁻¹) * (P.V.D.u * P.V.yi * P.V.D.u⁻¹) *
        (P.V.D.u * P.V.ki * P.V.D.u⁻¹)) * c⁻¹ by group, P.V.u_conj_t, P.V.u_conj_yi,
      P.V.u_conj_ki, P.V.E_comm hcE hmem, mul_inv_cancel_right]
  have h3 := h2.symm.trans h1
  obtain ⟨φ, e0, e1, e2, e3⟩ := P.V.exists_evE
  have key : S.z = (t * (S.z * P.V.yi) * P.V.ki) * (t * P.V.yi * P.V.ki) := by
    elem_eq φ e1 e2 e3 e0
  have key2 : (t * P.V.yi * P.V.ki) * (t * P.V.yi * P.V.ki) = 1 := by
    elem_eq φ e1 e2 e3 e0
  rw [h3, key2] at key
  exact z_ne_one S key

theorem exists_e : ∃ c ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X),
    P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ = c * P.V.yi * P.V.D.w₁ * P.V.D.u := by
  have hmem := P.V.comm_mem P.V.w₂_mem_S₁ P.V.u_mem_S₁
  rcases P.V.mem_E0w hmem with h | h
  · exact absurd h P.wu_not_mem_E0
  set e := P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * P.V.D.u⁻¹ * P.V.D.w₁⁻¹ with he
  have hwu : P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ = e * P.V.D.w₁ * P.V.D.u := by rw [he]; group
  have hw₁ := P.V.w₁_mul
  have hsq : (e * P.V.D.w₁ * P.V.D.u) * (e * P.V.D.w₁ * P.V.D.u) = 1 := by
    rw [← hwu, show P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) =
      P.V.D.w₂ * (P.V.D.u * P.V.D.u) * P.V.D.w₂⁻¹ by group, P.V.u_sq, mul_one,
      mul_inv_cancel]
  have hform : (e * P.V.D.w₁ * P.V.D.u) * (e * P.V.D.w₁ * P.V.D.u) =
      e * (P.V.D.w₁ * (P.V.D.u * e * P.V.D.u⁻¹) * P.V.D.w₁⁻¹) * (S.z * P.V.ki) := by
    calc (e * P.V.D.w₁ * P.V.D.u) * (e * P.V.D.w₁ * P.V.D.u) =
        e * (P.V.D.w₁ * (P.V.D.u * e * P.V.D.u⁻¹) * P.V.D.w₁⁻¹) *
          (P.V.D.w₁ * (P.V.D.u * P.V.D.w₁ * P.V.D.u⁻¹)) * (P.V.D.u * P.V.D.u) := by group
      _ = _ := by
          rw [P.u_conj_w₁, P.V.u_sq, mul_one, ← mul_assoc P.V.D.w₁ P.V.D.w₁, hw₁, one_mul]
  rcases P.V.mem_E0_cases h with h' | h'
  · exfalso
    have hB := P.V.zk_le_B h'
    rw [hform, P.V.u_conj_B hB, P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki h',
      ← pow_two, sq_of_mem_B S hB, one_mul] at hsq
    apply P.V.ki_ne_z
    calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, zz S, one_mul]
      _ = S.z := by rw [hsq, mul_one]
  · refine ⟨e * P.V.yi, h', ?_⟩
    rw [hwu, mul_assoc e P.V.yi P.V.yi, P.V.yi_sq, mul_one]

theorem w₂_conj_zk_eq {c : X} (hc : c = 1 ∨ c = S.z ∨ c = P.V.ki ∨ c = S.z * P.V.ki) :
    P.V.D.w₂ * c * P.V.D.w₂⁻¹ = 1 ∧ c = 1 ∨ P.V.D.w₂ * c * P.V.D.w₂⁻¹ = S.z * P.V.ki ∧ c = S.z ∨
      P.V.D.w₂ * c * P.V.D.w₂⁻¹ = P.V.ki ∧ c = P.V.ki ∨
        P.V.D.w₂ * c * P.V.D.w₂⁻¹ = S.z ∧ c = S.z * P.V.ki := by
  rcases hc with rfl | rfl | rfl | rfl
  · left; exact ⟨by group, rfl⟩
  · right; left; exact ⟨P.V.w₂_conj_z, rfl⟩
  · right; right; left; exact ⟨P.V.w₂_conj_ki, rfl⟩
  · right; right; right
    refine ⟨?_, rfl⟩
    rw [show P.V.D.w₂ * (S.z * P.V.ki) * P.V.D.w₂⁻¹ = (P.V.D.w₂ * S.z * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * P.V.ki * P.V.D.w₂⁻¹) by group, P.V.w₂_conj_z, P.V.w₂_conj_ki, mul_assoc,
      P.V.ki_sq, mul_one]

end CPair

end KD8c

end CFSG.ComponentClassification.HSFLit
