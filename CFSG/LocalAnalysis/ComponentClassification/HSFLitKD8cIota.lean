module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cRel4

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace CPair

variable (P : CPair S T₁)

noncomputable def ι : MC →* X := Classical.choose (MC.exists_hom P.pcX)

theorem ι_spec : P.ι MC.w₂ = P.w₂N ∧ P.ι MC.u = P.V.D.u ∧ P.ι MC.w₁ = P.w₁N ∧
    P.ι MC.v = P.V.vN ∧ P.ι MC.z = S.z ∧ P.ι MC.y = P.V.yi ∧ P.ι MC.t = t ∧
      P.ι MC.k = P.V.ki :=
  Classical.choose_spec (MC.exists_hom P.pcX)

theorem ι_w₂ : P.ι MC.w₂ = P.w₂N := P.ι_spec.1
theorem ι_u : P.ι MC.u = P.V.D.u := P.ι_spec.2.1
theorem ι_w₁ : P.ι MC.w₁ = P.w₁N := P.ι_spec.2.2.1
theorem ι_v : P.ι MC.v = P.V.vN := P.ι_spec.2.2.2.1
theorem ι_z : P.ι MC.z = S.z := P.ι_spec.2.2.2.2.1
theorem ι_y : P.ι MC.y = P.V.yi := P.ι_spec.2.2.2.2.2.1
theorem ι_t : P.ι MC.t = t := P.ι_spec.2.2.2.2.2.2.1
theorem ι_k : P.ι MC.k = P.V.ki := P.ι_spec.2.2.2.2.2.2.2

theorem ι_injective : Function.Injective P.ι :=
  MC.injective_of P.ι (by rw [P.ι_k]; exact P.V.ki_ne_one)

theorem yi_mem_S₁ : P.V.yi ∈ P.V.D.S₁ := P.V.E_le_S₁ (Frame.yi_mem_E _)

theorem B_le_S₁ : S.B ≤ P.V.D.S₁ := (B_le_E' S P.V.yi).trans P.V.E_le_S₁

theorem w₂N_mem_S₁ : P.w₂N ∈ P.V.D.S₁ := by
  rcases P.w₂N_eq with h | h <;> rw [h]
  · exact P.V.w₂_mem_S₁
  · exact mul_mem P.yi_mem_S₁ P.V.w₂_mem_S₁

theorem cN_mem_S₁ : P.cN ∈ P.V.D.S₁ := P.B_le_S₁ P.cN_mem_B

theorem w₁N_mem_S₁ : P.w₁N ∈ P.V.D.S₁ := by
  rw [P.w₁N_eq]; exact mul_mem P.V.w₁_mem_S₁ P.cN_mem_S₁

theorem range_ι : P.ι.range = P.V.D.S₁ := by
  apply le_antisymm
  · refine MC.range_le P.ι fun g hg => ?_
    simp only [MC.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [P.ι_w₂]; exact P.w₂N_mem_S₁
    · rw [P.ι_u]; exact P.V.u_mem_S₁
    · rw [P.ι_w₁]; exact P.w₁N_mem_S₁
    · rw [P.ι_v]; exact P.V.vN_mem_S₁
    · rw [P.ι_z]; exact P.B_le_S₁ Frame.z_mem_B
    · rw [P.ι_y]; exact P.yi_mem_S₁
    · rw [P.ι_t]; exact P.B_le_S₁ Frame.t_mem_B
    · rw [P.ι_k]; exact P.B_le_S₁ P.V.ki_mem_B
  · have hz : S.z ∈ P.ι.range := ⟨MC.z, P.ι_z⟩
    have hy : P.V.yi ∈ P.ι.range := ⟨MC.y, P.ι_y⟩
    have ht : t ∈ P.ι.range := ⟨MC.t, P.ι_t⟩
    have hk : P.V.ki ∈ P.ι.range := ⟨MC.k, P.ι_k⟩
    have hv : P.V.vN ∈ P.ι.range := ⟨MC.v, P.ι_v⟩
    have hB : S.B ≤ P.ι.range := by
      rw [P.V.B_eq']
      exact sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hk)) (zpowers_le.mpr ht)
    have hcN : P.cN ∈ P.ι.range := hB P.cN_mem_B
    rw [P.V.D.S₁_eq]
    refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) (zpowers_le.mpr ⟨MC.u, P.ι_u⟩)
    · have hE : S.E P.V.F.yF = S.E0 P.V.F.yF P.V.F.kF ⊔ zpowers t := P.V.F.E_eq
      change S.E P.V.F.yF ≤ _
      rw [hE, P.V.F.E0_eq]
      exact sup_le (sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hy))
        (zpowers_le.mpr hk)) (zpowers_le.mpr ht)
    · refine zpowers_le.mpr ?_
      rcases P.V.vN_eq with h | h
      · rw [← h]; exact hv
      · have : P.V.D.v = P.V.vN * t⁻¹ := by rw [h]; group
        rw [this]; exact mul_mem hv (inv_mem ht)
    · refine zpowers_le.mpr ?_
      have : P.V.D.w₁ = P.w₁N * P.cN⁻¹ := by rw [P.w₁N_eq]; group
      rw [this]; exact mul_mem ⟨MC.w₁, P.ι_w₁⟩ (inv_mem hcN)
    · refine zpowers_le.mpr ?_
      rcases P.w₂N_eq with h | h
      · rw [← h]; exact ⟨MC.w₂, P.ι_w₂⟩
      · have : P.V.D.w₂ = P.V.yi⁻¹ * P.w₂N := by rw [h]; group
        rw [this]; exact mul_mem (inv_mem hy) ⟨MC.w₂, P.ι_w₂⟩

theorem card_S₁ : Nat.card P.V.D.S₁ = 256 := by
  rw [← P.range_ι, ← Nat.card_congr (MonoidHom.ofInjective P.ι_injective).toEquiv,
    MC.card_eq]
  norm_num

end CPair

variable (S)

@[expose] def side₁ (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (hq₁ : D₁.q0 = .extraspecial)
    (hq₂ : D₂.q0 = .extraspecial) : VSide S T₁ where
  yi := S.y
  ki := S.k
  ui := S.x * S.y
  hyi := isRefl_y S
  hki := Or.inl rfl
  hui := rfl
  D := D₁
  hq := hq₁
  hu := u₁_eq S h4 D₁ D₂ hq₁ hq₂
  h4 := h4

@[expose] def side₂ (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (hq₁ : D₁.q0 = .extraspecial)
    (hq₂ : D₂.q0 = .extraspecial) : VSide S T₁ where
  yi := S.x * S.y
  ki := S.z * S.k
  ui := S.z * S.y
  hyi := isRefl_xy S
  hki := Or.inr rfl
  hui := by rw [← mul_assoc, xx S]
  D := D₂
  hq := hq₂
  hu := u₂_eq S h4 D₁ D₂ hq₁ hq₂
  h4 := h4

@[expose] def pair₁ (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)) (hq₁ : D₁.q0 = .extraspecial)
    (hq₂ : D₂.q0 = .extraspecial) : CPair S T₁ where
  V := side₁ S h4 D₁ D₂ hq₁ hq₂
  W := side₂ S h4 D₁ D₂ hq₁ hq₂
  hyy := rfl
  hkk := rfl

end KD8c

end CFSG.ComponentClassification.HSFLit
