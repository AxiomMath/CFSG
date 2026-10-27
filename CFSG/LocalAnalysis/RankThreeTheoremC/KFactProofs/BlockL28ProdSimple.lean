module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open scoped commutatorElement

theorem eq_top_of_normal_of_proj_surjective {U₁ U₂ : Type*} [Group U₁] [Group U₂]
    [IsSimpleGroup U₁] [IsSimpleGroup U₂] (h₁ : ∃ a b : U₁, a * b ≠ b * a)
    (h₂ : ∃ a b : U₂, a * b ≠ b * a) {W : Subgroup (U₁ × U₂)} [hW : W.Normal]
    (hW₁ : ∀ u : U₁, ∃ w ∈ W, w.1 = u) (hW₂ : ∀ u : U₂, ∃ w ∈ W, w.2 = u) : W = ⊤ := by
  have hx : ∀ x : U₁, (x, (1 : U₂)) ∈ W := by
    have : (W.comap (MonoidHom.inl U₁ U₂)).Normal := hW.comap _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.comap (MonoidHom.inl U₁ U₂)) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := h₁
      obtain ⟨w, hwW, hwa⟩ := hW₁ a
      have hc : (⁅w, ((b : U₁), (1 : U₂))⁆ : U₁ × U₂) ∈ W := by
        rw [commutatorElement_def]
        have := hW.conj_mem (w⁻¹) (W.inv_mem hwW) ((b : U₁), (1 : U₂))
        have h2 : ((b : U₁), (1 : U₂)) * w⁻¹ * ((b : U₁), (1 : U₂))⁻¹ ∈ W := this
        simpa [mul_assoc] using W.mul_mem hwW h2
      have hc2 : (⁅a, b⁆, (1 : U₂)) ∈ W := by
        have e : (⁅w, ((b : U₁), (1 : U₂))⁆ : U₁ × U₂) = (⁅a, b⁆, (1 : U₂)) := by
          ext
          · simp [commutatorElement_def, hwa]
          · simp [commutatorElement_def]
        rwa [e] at hc
      have h3 : ⁅a, b⁆ ∈ W.comap (MonoidHom.inl U₁ U₂) := hc2
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
      exact hab h3
    · intro x
      have : x ∈ W.comap (MonoidHom.inl U₁ U₂) := h ▸ Subgroup.mem_top x
      exact this
  have hy : ∀ y : U₂, ((1 : U₁), y) ∈ W := by
    have : (W.comap (MonoidHom.inr U₁ U₂)).Normal := hW.comap _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.comap (MonoidHom.inr U₁ U₂)) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := h₂
      obtain ⟨w, hwW, hwa⟩ := hW₂ a
      have hc : (⁅w, ((1 : U₁), (b : U₂))⁆ : U₁ × U₂) ∈ W := by
        rw [commutatorElement_def]
        have := hW.conj_mem (w⁻¹) (W.inv_mem hwW) ((1 : U₁), (b : U₂))
        have h2 : ((1 : U₁), (b : U₂)) * w⁻¹ * ((1 : U₁), (b : U₂))⁻¹ ∈ W := this
        simpa [mul_assoc] using W.mul_mem hwW h2
      have hc2 : ((1 : U₁), ⁅a, b⁆) ∈ W := by
        have e : (⁅w, ((1 : U₁), (b : U₂))⁆ : U₁ × U₂) = ((1 : U₁), ⁅a, b⁆) := by
          ext
          · simp [commutatorElement_def]
          · simp [commutatorElement_def, hwa]
        rwa [e] at hc
      have h3 : ⁅a, b⁆ ∈ W.comap (MonoidHom.inr U₁ U₂) := hc2
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
      exact hab h3
    · intro y
      have : y ∈ W.comap (MonoidHom.inr U₁ U₂) := h ▸ Subgroup.mem_top y
      exact this
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have := W.mul_mem (hx x) (hy y)
  simpa using this

theorem not_exists_surjective_quasisimple_prod {S U₁ U₂ : Type} [Group S] [Group U₁] [Group U₂]
    [IsSimpleGroup U₁] [IsSimpleGroup U₂] (h₁ : ∃ a b : U₁, a * b ≠ b * a)
    (h₂ : ∃ a b : U₂, a * b ≠ b * a) (hS : CFSG.Open.IsQuasisimple S) (σ : S →* U₁ × U₂)
    (hσ : Function.Surjective σ) : False := by
  have hZ₁ : ∀ x : U₁, (∀ y : U₁, y * x = x * y) → x = 1 := by
    intro x hx
    have hc : Subgroup.center U₁ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U₁) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := h₁
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have : x ∈ Subgroup.center U₁ := Subgroup.mem_center_iff.mpr hx
    rwa [hc, Subgroup.mem_bot] at this
  have hZ₂ : ∀ x : U₂, (∀ y : U₂, y * x = x * y) → x = 1 := by
    intro x hx
    have hc : Subgroup.center U₂ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U₂) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := h₂
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have : x ∈ Subgroup.center U₂ := Subgroup.mem_center_iff.mpr hx
    rwa [hc, Subgroup.mem_bot] at this
  haveI := IsSimpleGroup.toNontrivial (G := U₁)
  haveI := IsSimpleGroup.toNontrivial (G := U₂)
  obtain ⟨x, hx⟩ := exists_ne (1 : U₁)
  obtain ⟨y, hy⟩ := exists_ne (1 : U₂)
  rcases CFSG.AGLEmbedding.le_center_or_eq_top_of_normal_quasisimple hS σ.ker with hk | hk
  ·
    have hkZ : σ.ker = Subgroup.center S := by
      refine le_antisymm hk fun z hz => ?_
      rw [MonoidHom.mem_ker]
      refine Prod.ext (hZ₁ _ fun u => ?_) (hZ₂ _ fun u => ?_)
      · obtain ⟨s, hs⟩ := hσ (u, (1 : U₂))
        have := congrArg Prod.fst (congrArg σ (Subgroup.mem_center_iff.mp hz s))
        simpa [hs] using this
      · obtain ⟨s, hs⟩ := hσ ((1 : U₁), u)
        have := congrArg Prod.snd (congrArg σ (Subgroup.mem_center_iff.mp hz s))
        simpa [hs] using this
    have e : S ⧸ Subgroup.center S ≃* U₁ × U₂ :=
      (QuotientGroup.quotientMulEquivOfEq hkZ.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective σ hσ)
    have hsimple : IsSimpleGroup (U₁ × U₂) := by
      have := hS.2
      exact e.symm.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.snd U₁ U₂).ker with h | h
    · have : (x, (1 : U₂)) ∈ (MonoidHom.snd U₁ U₂).ker := rfl
      rw [h, Subgroup.mem_bot] at this
      exact hx (congrArg Prod.fst this)
    · have : ((1 : U₁), y) ∈ (MonoidHom.snd U₁ U₂).ker := h ▸ Subgroup.mem_top _
      exact hy this
  ·
    obtain ⟨s, hs⟩ := hσ (x, (1 : U₂))
    have : s ∈ σ.ker := hk ▸ Subgroup.mem_top s
    rw [MonoidHom.mem_ker, hs] at this
    exact hx (congrArg Prod.fst this)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
