module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqComp

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5

variable {G : Type} [Group G] [Finite G]

theorem card_four {C S K₁ K₂ K₃ K₄ : Subgroup G} (hS : IsPGroup 2 S)
    (h₁ : K₁ ≤ C) (h₂ : K₂ ≤ C) (h₃ : K₃ ≤ C) (h₄ : K₄ ≤ C)
    (p₁ : IsPComponent 2 (K₁.subgroupOf C)) (p₂ : IsPComponent 2 (K₂.subgroupOf C))
    (p₃ : IsPComponent 2 (K₃.subgroupOf C)) (p₄ : IsPComponent 2 (K₄.subgroupOf C))
    (n₁₂ : K₁ ≠ K₂) (n₁₃ : K₁ ≠ K₃) (n₁₄ : K₁ ≠ K₄) (n₂₃ : K₂ ≠ K₃) (n₂₄ : K₂ ≠ K₄)
    (n₃₄ : K₃ ≠ K₄) {e₁ e₂ e₃ e₄ : G} (s₁ : e₁ ∈ S) (s₂ : e₂ ∈ S) (s₃ : e₃ ∈ S) (s₄ : e₄ ∈ S)
    (k₁ : e₁ ∈ K₁) (k₂ : e₂ ∈ K₂) (k₃ : e₃ ∈ K₃) (k₄ : e₄ ∈ K₄) (i₁ : e₁ * e₁ = 1)
    (i₂ : e₂ * e₂ = 1) (i₃ : e₃ * e₃ = 1) (i₄ : e₄ * e₄ = 1)
    (o₁ : e₁ ∉ coreActionKernel K₁) (o₂ : e₂ ∉ coreActionKernel K₂)
    (o₃ : e₃ ∉ coreActionKernel K₃) (o₄ : e₄ ∉ coreActionKernel K₄) :
    IsElemTwo (zpowers e₁ ⊔ (zpowers e₄ ⊔ (zpowers e₃ ⊔ zpowers e₂))) ∧
      Nat.card ↥(zpowers e₁ ⊔ (zpowers e₄ ⊔ (zpowers e₃ ⊔ zpowers e₂))) = 16 ∧
      zpowers e₄ ⊔ (zpowers e₃ ⊔ zpowers e₂) ≤ coreActionKernel K₁ := by
  have cm : ∀ {K K' : Subgroup G} {x y : G}, K ≤ C → K' ≤ C → IsPComponent 2 (K.subgroupOf C) →
      IsPComponent 2 (K'.subgroupOf C) → K ≠ K' → x ∈ S → x ∈ K → y ∈ S → y ∈ K' →
      x * y = y * x := fun hK hK' pK pK' hne hxS hxK hyS hyK' =>
    commute_of_ne hK hK' pK pK' hne hS hxS hxK hyS hyK'
  have ck : ∀ {K K' : Subgroup G}, K ≤ C → K' ≤ C → IsPComponent 2 (K.subgroupOf C) →
      IsPComponent 2 (K'.subgroupOf C) → K ≠ K' → K' ≤ coreActionKernel K :=
    fun hK hK' pK pK' hne => le_coreActionKernel_of_ne hK hK' pK pK' hne
  have hz : ∀ {e : G}, e * e = 1 → IsElemTwo (zpowers e) := fun he => isElemTwo_zpowers he
  have c₃₂ : ∀ y ∈ zpowers e₂, e₃ * y = y * e₃ := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute e₃ e₂ from cm h₃ h₂ p₃ p₂ n₂₃.symm s₃ k₃ s₂ k₂) k).eq
  have n₃ : e₃ ∉ zpowers e₂ := fun h => o₃ (zpowers_le.mpr (ck h₃ h₂ p₃ p₂ n₂₃.symm k₂) h)
  obtain ⟨E₃, c₃⟩ := elemTwo_zpowers_sup i₃ (hz i₂) c₃₂ n₃
  have hc2 : Nat.card (zpowers e₂) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact i₂) fun h => o₂ (by
      rw [h]; exact one_mem _)
  have W₃K₄ : zpowers e₃ ⊔ zpowers e₂ ≤ coreActionKernel K₄ :=
    sup_le (zpowers_le.mpr (ck h₄ h₃ p₄ p₃ n₃₄.symm k₃))
      (zpowers_le.mpr (ck h₄ h₂ p₄ p₂ n₂₄.symm k₂))
  have c₄ : ∀ y ∈ zpowers e₃ ⊔ zpowers e₂, e₄ * y = y * e₄ := by
    have hle : zpowers e₃ ⊔ zpowers e₂ ≤ centralizer ({e₄} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (cm h₃ h₄ p₃ p₄ n₃₄ s₃ k₃ s₄ k₄)))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (cm h₂ h₄ p₂ p₄ n₂₄ s₂ k₂ s₄ k₄)))
    exact fun y hy => (mem_centralizer_singleton_iff.mp (hle hy)).symm
  obtain ⟨E₄, c₄'⟩ := elemTwo_zpowers_sup i₄ E₃ c₄ fun h => o₄ (W₃K₄ h)
  have WK₁ : zpowers e₄ ⊔ (zpowers e₃ ⊔ zpowers e₂) ≤ coreActionKernel K₁ :=
    sup_le (zpowers_le.mpr (ck h₁ h₄ p₁ p₄ n₁₄ k₄)) (sup_le
      (zpowers_le.mpr (ck h₁ h₃ p₁ p₃ n₁₃ k₃)) (zpowers_le.mpr (ck h₁ h₂ p₁ p₂ n₁₂ k₂)))
  have c₁ : ∀ y ∈ zpowers e₄ ⊔ (zpowers e₃ ⊔ zpowers e₂), e₁ * y = y * e₁ := by
    have hle : zpowers e₄ ⊔ (zpowers e₃ ⊔ zpowers e₂) ≤ centralizer ({e₁} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (cm h₄ h₁ p₄ p₁ n₁₄.symm s₄ k₄ s₁ k₁))) (sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (cm h₃ h₁ p₃ p₁ n₁₃.symm s₃ k₃ s₁ k₁)))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (cm h₂ h₁ p₂ p₁ n₁₂.symm s₂ k₂ s₁ k₁))))
    exact fun y hy => (mem_centralizer_singleton_iff.mp (hle hy)).symm
  obtain ⟨E₁, c₁'⟩ := elemTwo_zpowers_sup i₁ E₄ c₁ fun h => o₁ (WK₁ h)
  refine ⟨E₁, ?_, WK₁⟩
  rw [c₁', c₄', c₃, hc2]

end CFSG.ComponentClassification.HSFLit.L34Uniq
