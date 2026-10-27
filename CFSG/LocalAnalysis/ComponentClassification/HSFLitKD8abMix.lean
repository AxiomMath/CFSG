module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Tower
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abT

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem vw_conj {F : Frame S} {ui : X} (D : S.Sec6 T₁ F.yF F.kF ui) (hact : D.act = .one) :
    (D.v * D.w₁) * t * (D.v * D.w₁)⁻¹ = t * (S.z * F.kF) ∧
      ∀ e ∈ S.E0 F.yF F.kF, (D.v * D.w₁) * e * (D.v * D.w₁)⁻¹ = e := by
  have h := D.act_holds
  rw [hact] at h
  refine ⟨?_, fun e he => ?_⟩
  · calc (D.v * D.w₁) * t * (D.v * D.w₁)⁻¹ = D.v * (D.w₁ * t * D.w₁⁻¹) * D.v⁻¹ := by group
      _ = (D.v * t * D.v⁻¹) * (D.v * S.z * D.v⁻¹) := by rw [h.2.2.1]; group
      _ = t * (S.z * F.kF) := by
        rw [h.2.1, (h.1 _ F.z_mem_E0).1, mul_assoc, F.kF_comm_z]
  · calc (D.v * D.w₁) * e * (D.v * D.w₁)⁻¹ = D.v * (D.w₁ * e * D.w₁⁻¹) * D.v⁻¹ := by group
      _ = e := by rw [(h.1 e he).2.1, (h.1 e he).1]

theorem u_eq_of_act (h4 : S.Sec4 T₁) {F : Frame S} {ui : X} (huiR : ui ∈ A.R)
    (D : S.Sec6 T₁ F.yF F.kF ui) (hact : D.act = .one) {n : X} (hn : n ∈ T₁)
    (hnt : n * t * n⁻¹ = t * F.kF) (hnk : n * S.k * n⁻¹ = S.k)
    (hnu : n * ui * n⁻¹ = ui ∨ n * ui * n⁻¹ = S.z * ui) : D.u = ui := by
  rcases D.u_eq with h | h
  · exact h
  exfalso
  have hA := D.act_holds
  rw [hact] at hA
  have hvt : D.v * t * D.v⁻¹ = t * F.kF := hA.2.1
  have hvz : D.v * S.z * D.v⁻¹ = S.z := (hA.1 _ F.z_mem_E0).1
  have hvk : D.v * S.k * D.v⁻¹ = S.k := (hA.1 _ F.k_mem_E0).1
  have hvT₁ : D.v ∈ T₁ := D.T₁_eq.symm.le (mem_sup_left (mem_sup_right (mem_zpowers _)))
  have hvu : D.v * ui * D.v⁻¹ = F.kF * ui := by
    have hc : D.u * D.v = D.v * D.u := D.u_comm_C D.v (D.C_eq ▸ subset_closure (by simp))
    rw [h] at hc
    have h1 : D.v * (t * ui) * D.v⁻¹ = t * ui := by rw [← hc]; group
    rw [show D.v * (t * ui) * D.v⁻¹ = (D.v * t * D.v⁻¹) * (D.v * ui * D.v⁻¹) by group,
      hvt] at h1
    calc D.v * ui * D.v⁻¹ = (t * F.kF)⁻¹ * (t * F.kF * (D.v * ui * D.v⁻¹)) := by group
      _ = F.kF * ui := by
          rw [h1, mul_inv_rev, F.kF_inv, mul_assoc, inv_mul_cancel_left]
  set τ := D.v⁻¹ * n with hτdef
  have hτT₁ : τ ∈ T₁ := mul_mem (inv_mem hvT₁) hn
  have hτt : τ * t = t * τ := by
    have h1 : τ * t * τ⁻¹ = t := by
      calc τ * t * τ⁻¹ = D.v⁻¹ * (n * t * n⁻¹) * D.v := by rw [hτdef]; group
        _ = D.v⁻¹ * (D.v * t * D.v⁻¹) * D.v := by rw [hnt, hvt]
        _ = t := by group
    calc τ * t = τ * t * τ⁻¹ * τ := by group
      _ = t * τ := by rw [h1]
  have hτk : τ * S.k = S.k * τ := by
    have h1 : τ * S.k * τ⁻¹ = S.k := by
      calc τ * S.k * τ⁻¹ = D.v⁻¹ * (n * S.k * n⁻¹) * D.v := by rw [hτdef]; group
        _ = D.v⁻¹ * (D.v * S.k * D.v⁻¹) * D.v := by rw [hnk, hvk]
        _ = S.k := by group
    calc τ * S.k = τ * S.k * τ⁻¹ * τ := by group
      _ = S.k * τ := by rw [h1]
  have hτE := mem_TE_of_mem_T₁ S h4 hτT₁ hτt hτk
  have hτu : τ * ui * τ⁻¹ = ui ∨ τ * ui * τ⁻¹ = S.z * ui := by
    rcases commutator_TE S hτE (R_le_TE S huiR) with h1 | h1
    · left
      calc τ * ui * τ⁻¹ = τ * ui * τ⁻¹ * ui⁻¹ * ui := by group
        _ = ui := by rw [h1, one_mul]
    · right
      calc τ * ui * τ⁻¹ = τ * ui * τ⁻¹ * ui⁻¹ * ui := by group
        _ = S.z * ui := by rw [h1]
  have hn' : n = D.v * τ := by rw [hτdef]; group
  have hkz : F.kF ≠ 1 ∧ F.kF ≠ S.z := ⟨F.kF_ne_one, fun h' => F.kF_not_mem_z (h' ▸ mem_zpowers _)⟩
  have hnu' : n * ui * n⁻¹ = F.kF * ui ∨ n * ui * n⁻¹ = S.z * (F.kF * ui) := by
    rw [hn', show D.v * τ * ui * (D.v * τ)⁻¹ = D.v * (τ * ui * τ⁻¹) * D.v⁻¹ by group]
    rcases hτu with h1 | h1 <;> rw [h1]
    · exact Or.inl hvu
    · right
      rw [show D.v * (S.z * ui) * D.v⁻¹ = (D.v * S.z * D.v⁻¹) * (D.v * ui * D.v⁻¹) by group, hvz,
        hvu]
  rcases hnu with h1 | h1 <;> rcases hnu' with h2 | h2 <;> rw [h1] at h2
  · exact hkz.1 (mul_eq_right.mp h2.symm)
  · apply hkz.2
    have h3 : ui = S.z * F.kF * ui := by rw [mul_assoc]; exact h2
    have h4 : S.z * F.kF = 1 := mul_eq_right.mp h3.symm
    rw [eq_inv_of_mul_eq_one_right h4, z_inv S]
  · apply hkz.2
    exact mul_right_cancel h2.symm
  · apply hkz.1
    have h3 : S.z * ui = S.z * (F.kF * ui) := h2
    exact mul_eq_right.mp (mul_left_cancel h3).symm

variable (S)

theorem u_eq₁ (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (hact₁ : D₁.act = .one)
    (hact₂ : D₂.act = .one) : D₁.u = S.x * S.y := by
  obtain ⟨h1, h2⟩ := vw_conj (F := frame₂ S) D₂ hact₂
  refine u_eq_of_act (F := frame₁ S) h4 (isRefl_xy S).mem D₁ hact₁
    (mul_mem (D₂.T₁_eq.symm.le (mem_sup_left (mem_sup_right (mem_zpowers _))))
      (D₂.T₁_eq.symm.le (mem_sup_right (mem_zpowers _)))) ?_ ?_ (Or.inl ?_)
  · rw [h1]
    show t * (S.z * (S.z * S.k)) = t * S.k
    rw [← mul_assoc S.z, zz S, one_mul]
  · exact h2 _ (frame₂ S).k_mem_E0
  · exact h2 _ (frame₂ S).yF_mem_E0

theorem u_eq₂ (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (hact₁ : D₁.act = .one)
    (hact₂ : D₂.act = .one) : D₂.u = S.z * S.y := by
  obtain ⟨h1, h2⟩ := vw_conj (F := frame₁ S) D₁ hact₁
  have hzyR : S.z * S.y ∈ A.R := mul_mem (z_mem_R S) S.y_mem
  refine u_eq_of_act (F := frame₂ S) h4 hzyR D₂ hact₂
    (mul_mem (D₁.T₁_eq.symm.le (mem_sup_left (mem_sup_right (mem_zpowers _))))
      (D₁.T₁_eq.symm.le (mem_sup_right (mem_zpowers _)))) h1 ?_ (Or.inl ?_)
  · exact h2 _ (frame₁ S).k_mem_E0
  · exact h2 _ (mul_mem (frame₁ S).z_mem_E0 (frame₁ S).yF_mem_E0)

end KD8ab

end CFSG.ComponentClassification.HSFLit
