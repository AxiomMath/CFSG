module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7End3

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

@[expose] def swapFrame (F : S.Frame) (hfix : ∀ n ∈ normalizer (S.E (F.xF * F.yF) : Set X),
    n * (S.z * F.kF) * n⁻¹ = S.z * F.kF) : S.Frame where
  xF := F.xF⁻¹
  yF := F.xF * F.yF
  kF := S.z * F.kF
  xF_mem := inv_mem F.xF_mem
  yF_mem := xyF_mem_R F
  xF_sq := by rw [inv_pow, F.xF_sq, inv_eq_of_mul_eq_one_right (zz S)]
  yF_sq := xyF_sq F
  yF_inv := by
    calc F.xF * F.yF * F.xF⁻¹ * (F.xF * F.yF)⁻¹ = F.xF * (F.yF * F.xF * F.yF⁻¹)⁻¹ * F.xF⁻¹ := by
          group
      _ = F.xF⁻¹⁻¹ := by rw [F.yF_inv]; group
  kF_mem := mul_mem z_mem_T F.kF_mem
  kF_sq := (isK_zkF F).sq
  kF_comm := fun r hr => S.central_of_mem_B (mul_mem z_mem_B (kF_mem_B F)) hr.1
  kF_not_mem := fun h => F.kF_not_mem (by
    have := mul_mem (inv_mem (mem_sup_left S.z_mem)) h
    rwa [inv_mul_cancel_left] at this)
  kF_fixed := fun n hn => hfix n hn.1

theorem sec4_swapFrame {F : S.Frame} {T₁ : Subgroup X} (h4 : S.Sec4 F T₁)
    (hfix : ∀ n ∈ normalizer (S.E (F.xF * F.yF) : Set X), n * (S.z * F.kF) * n⁻¹ = S.z * F.kF) :
    S.Sec4 (swapFrame F hfix) T₁ where
  isPGroup := h4.isPGroup
  le := h4.le
  le_normalizer := h4.le_normalizer
  maximal := h4.maximal
  card := h4.card
  fusion := fun b hb => by
    rw [h4.fusion b hb]
    show _ ↔ (b = S.t ∨ b = S.t * S.z ∨ b = S.t * (S.z * F.kF) ∨
      b = S.t * S.z * (S.z * F.kF))
    rw [show S.t * (S.z * F.kF) = S.t * S.z * F.kF by group,
      show S.t * S.z * (S.z * F.kF) = S.t * F.kF by
        rw [show S.t * S.z * (S.z * F.kF) = S.t * (S.z * S.z) * F.kF by group, zz S, mul_one]]
    tauto

theorem hnc_swapFrame {F : S.Frame} (hnc : ¬ SubConj F.E₁ F.E₂)
    (hfix : ∀ n ∈ normalizer (S.E (F.xF * F.yF) : Set X), n * (S.z * F.kF) * n⁻¹ = S.z * F.kF) :
    ¬ SubConj (swapFrame F hfix).E₁ (swapFrame F hfix).E₂ := by
  rintro ⟨g, hg⟩
  apply hnc
  refine ⟨g⁻¹, ?_⟩
  have e : (swapFrame F hfix).E₂ = F.E₁ := by
    show S.E (F.xF⁻¹ * (F.xF * F.yF)) = S.E F.yF
    rw [inv_mul_cancel_left]
  rw [e] at hg
  exact act_inv_eq hg

theorem false_of_side₂ [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) {F : S.Frame}
    {T₁ : Subgroup X} (h4 : S.Sec4 F T₁) (hnc : ¬ SubConj F.E₁ F.E₂)
    (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF))
    (hq : D₂.q0 = .e4q8 ∨ D₂.q0 = .exceptional) : False := by
  have e1 : F.xF⁻¹ * (F.xF * F.yF) = F.yF := inv_mul_cancel_left _ _
  have e2 : S.z * (S.z * F.kF) = F.kF := by rw [← mul_assoc, zz S, one_mul]
  have hT : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF) =
      S.Sec6 T₁ (F.xF⁻¹ * (F.xF * F.yF)) (S.z * (S.z * F.kF)) (F.xF * F.yF) := by rw [e1, e2]
  let C : Setup S :=
    { F := swapFrame F D₂.k_fixed
      T₁ := T₁
      h4 := sec4_swapFrame h4 D₂.k_fixed
      hnc := hnc_swapFrame hnc D₂.k_fixed
      u₁ := S.z * F.yF
      u₂ := F.xF * F.yF
      hu₁ := Or.inr (by show S.z * F.yF = S.z * (F.xF⁻¹ * (F.xF * F.yF)); rw [e1])
      hu₂ := Or.inr rfl
      D₁ := D₂
      D₂ := cast hT D₁
      hq := hq }
  exact C.false_of_exc hnab

end Sec7

theorem fritzA7Section7 : FritzA7Section7 := by
  intro _ X _ _ _ hnab _ S F T₁ h4 hnc D₁ D₂ hq
  rcases hq with h | h | h | h
  · exact Sec7.Setup.false_of_exc ⟨F, T₁, h4, hnc, _, _, Or.inl rfl, Or.inl rfl, D₁, D₂,
      Or.inl h⟩ hnab
  · exact Sec7.Setup.false_of_exc ⟨F, T₁, h4, hnc, _, _, Or.inl rfl, Or.inl rfl, D₁, D₂,
      Or.inr h⟩ hnab
  · exact Sec7.false_of_side₂ hnab h4 hnc D₁ D₂ (Or.inl h)
  · exact Sec7.false_of_side₂ hnab h4 hnc D₁ D₂ (Or.inr h)

end CFSG.ComponentClassification.HSFLit
