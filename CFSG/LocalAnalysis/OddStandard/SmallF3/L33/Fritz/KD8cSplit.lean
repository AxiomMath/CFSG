module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abMixV

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem act_two_of_extra {yi ki ui : X} (D : S.Sec6 T₁ yi ki ui) (hq : D.q0 = .extraspecial) :
    S.ActHolds yi ki D.v D.w₁ D.w₂ .two := by
  have h := D.q0_holds
  rw [hq] at h
  exact h.2.2.1

theorem u_eq_t_mul_of_act (h4 : S.Sec4 T₁) {F : Frame S} {ui : X} (huiR : ui ∈ A.R)
    (D : S.Sec6 T₁ F.yF F.kF ui) (hq : D.q0 = .extraspecial) {n : X} (hn : n ∈ T₁)
    (hnt : n * t * n⁻¹ = t * F.kF) (hnk : n * S.k * n⁻¹ = S.k)
    (hnu : n * ui * n⁻¹ = F.kF * ui ∨ n * ui * n⁻¹ = S.z * (F.kF * ui)) : D.u = t * ui := by
  rcases D.u_eq with h | h
  swap
  · exact h
  exfalso
  have hA := act_two_of_extra D hq
  have hvt : D.v * t * D.v⁻¹ = t * F.kF := hA.2.1
  have hvz : D.v * S.z * D.v⁻¹ = S.z := hA.1 _ F.z_mem_E0
  have hvk : D.v * S.k * D.v⁻¹ = S.k := hA.1 _ F.k_mem_E0
  have hvT₁ : D.v ∈ T₁ := D.T₁_eq.symm.le (mem_sup_left (mem_sup_right (mem_zpowers _)))
  have hvu : D.v * ui * D.v⁻¹ = ui := by
    have hc : D.u * D.v = D.v * D.u := D.u_comm_C D.v (D.C_eq ▸ subset_closure (by simp))
    rw [h] at hc
    rw [← hc]; group
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
  have hnu' : n * ui * n⁻¹ = ui ∨ n * ui * n⁻¹ = S.z * ui := by
    rw [hn', show D.v * τ * ui * (D.v * τ)⁻¹ = D.v * (τ * ui * τ⁻¹) * D.v⁻¹ by group]
    rcases hτu with h1 | h1 <;> rw [h1]
    · exact Or.inl hvu
    · right
      rw [show D.v * (S.z * ui) * D.v⁻¹ = (D.v * S.z * D.v⁻¹) * (D.v * ui * D.v⁻¹) by group, hvz,
        hvu]
  have hkz : F.kF ≠ 1 ∧ F.kF ≠ S.z :=
    ⟨F.kF_ne_one, fun h' => F.kF_not_mem_z (h' ▸ mem_zpowers _)⟩
  rcases hnu with h1 | h1 <;> rcases hnu' with h2 | h2 <;> rw [h1] at h2
  · exact hkz.1 (mul_eq_right.mp h2)
  · exact hkz.2 (mul_right_cancel h2)
  · apply hkz.2
    have h3 : S.z * F.kF * ui = 1 * ui := by rw [one_mul, mul_assoc]; exact h2
    rw [eq_inv_of_mul_eq_one_right (mul_right_cancel h3), z_inv S]
  · exact hkz.1 (mul_eq_right.mp (mul_left_cancel h2))

variable (S)

theorem u₁_eq (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (hq₁ : D₁.q0 = .extraspecial)
    (hq₂ : D₂.q0 = .extraspecial) : D₁.u = t * (S.x * S.y) := by
  obtain ⟨-, -, hw₁t, -, hw₁z, -, -, hw₁y, hw₁k, -⟩ := act_two_of_extra D₂ hq₂
  have hxyR : S.x * S.y ∈ A.R := (isRefl_xy S).mem
  refine u_eq_t_mul_of_act (F := frame₁ S) h4 hxyR D₁ hq₁
    (D₂.T₁_eq.symm.le (mem_sup_right (mem_zpowers _))) ?_ ?_ (Or.inr ?_)
  · rw [hw₁t]
    show t * S.z * (S.z * S.k) = t * S.k
    rw [mul_assoc t, ← mul_assoc S.z, zz S, one_mul]
  · have e : S.k = S.z * (S.z * S.k) := by rw [← mul_assoc, zz S, one_mul]
    have he : D₂.w₁ * S.k * D₂.w₁⁻¹ = D₂.w₁ * (S.z * (S.z * S.k)) * D₂.w₁⁻¹ :=
      congrArg (fun a => D₂.w₁ * a * D₂.w₁⁻¹) e
    rw [he, show D₂.w₁ * (S.z * (S.z * S.k)) * D₂.w₁⁻¹ =
      (D₂.w₁ * S.z * D₂.w₁⁻¹) * (D₂.w₁ * (S.z * S.k) * D₂.w₁⁻¹) by group, hw₁z, hw₁k,
      ← mul_assoc, zz S, one_mul]
  · rw [hw₁y]
    show S.x * S.y * (S.z * S.k) = S.z * (S.k * (S.x * S.y))
    rw [← central_of_mem_B S (mul_mem Frame.z_mem_B Frame.k_mem_B) (R_le_TE S hxyR), mul_assoc]

theorem u₂_eq (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (hq₁ : D₁.q0 = .extraspecial)
    (hq₂ : D₂.q0 = .extraspecial) : D₂.u = t * (S.z * S.y) := by
  obtain ⟨-, -, hw₁t, -, hw₁z, -, -, hw₁y, hw₁k, -⟩ := act_two_of_extra D₁ hq₁
  have hzyR : S.z * S.y ∈ A.R := mul_mem (z_mem_R S) S.y_mem
  refine u_eq_t_mul_of_act (F := frame₂ S) h4 hzyR D₂ hq₂
    (D₁.T₁_eq.symm.le (mem_sup_right (mem_zpowers _))) ?_ hw₁k (Or.inr ?_)
  · rw [hw₁t, mul_assoc]
    rfl
  · rw [show D₁.w₁ * (S.z * S.y) * D₁.w₁⁻¹ = (D₁.w₁ * S.z * D₁.w₁⁻¹) * (D₁.w₁ * S.y * D₁.w₁⁻¹)
      by group, hw₁z, hw₁y]
    show S.z * (S.y * S.k) = S.z * (S.z * S.k * (S.z * S.y))
    have hk := central_of_mem_B S Frame.k_mem_B (R_le_TE S S.y_mem)
    have hkz := central_of_mem_B S Frame.k_mem_B (R_le_TE S (z_mem_R S))
    congr 1
    calc S.y * S.k = (S.z * S.z) * (S.k * S.y) := by rw [zz S, one_mul, hk]
      _ = S.z * (S.z * S.k) * S.y := by group
      _ = S.z * (S.k * S.z) * S.y := by rw [hkz]
      _ = S.z * S.k * (S.z * S.y) := by group

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
