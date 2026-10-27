module

public import CFSG.LinearAlgebra.RootGroupSL.ModelDefs


public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀]
variable [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

theorem modelIota_apply (e₀ : VJ) (t : E) : modelIota k V₀ e₀ t = (t • e₀, 0) := by
  rfl

theorem modelPi_apply (l₀ : VJ →ₗ[E] E) (v : VJ) (w : V₀) : modelPi k V₀ l₀ (v, w) = l₀ v := by
  rfl

theorem modelA1Elt_apply (φ : V₀ →ₗ[k] VJ) (v : VJ) (w : V₀) :
    modelA1Elt φ (v, w) = (v + φ w, w) := by
  rfl

theorem modelA2Elt_apply (ψ : VJ →ₗ[k] V₀) (v : VJ) (w : V₀) :
    modelA2Elt ψ (v, w) = (v, w + ψ v) := by
  rfl

theorem modelA1Elt_add (φ φ' : V₀ →ₗ[k] VJ) :
    modelA1Elt (φ + φ') = modelA1Elt φ * modelA1Elt φ' := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  simp [modelA1Elt_apply, add_assoc, add_comm, add_left_comm]

theorem modelA2Elt_add (ψ ψ' : VJ →ₗ[k] V₀) :
    modelA2Elt (ψ + ψ') = modelA2Elt ψ * modelA2Elt ψ' := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  simp [modelA2Elt_apply, add_assoc, add_comm, add_left_comm]

theorem modelA1Elt_injective :
    Function.Injective (modelA1Elt : (V₀ →ₗ[k] VJ) → SpecialLinearGroup k (VJ × V₀)) := by
  intro φ φ' h
  ext w
  have hw := congrArg (fun g : SpecialLinearGroup k (VJ × V₀) => g (0, w)) h
  simpa [modelA1Elt_apply] using hw

theorem modelA2Elt_injective :
    Function.Injective (modelA2Elt : (VJ →ₗ[k] V₀) → SpecialLinearGroup k (VJ × V₀)) := by
  intro ψ ψ' h
  ext v
  have hv := congrArg (fun g : SpecialLinearGroup k (VJ × V₀) => g (v, 0)) h
  simpa [modelA2Elt_apply] using hv

theorem mem_modelA1_iff (g : SpecialLinearGroup k (VJ × V₀)) :
    g ∈ modelA1 k VJ V₀ ↔ ∃ φ : V₀ →ₗ[k] VJ, modelA1Elt φ = g := by
  constructor
  · rintro ⟨hzero, hsecond⟩
    let φ : V₀ →ₗ[k] VJ :=
      (LinearMap.fst k VJ V₀).comp
        ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inr k VJ V₀))
    refine ⟨φ, ?_⟩
    apply SpecialLinearGroup.ext
    intro p
    obtain ⟨v, w⟩ := p
    have h1 : g (v, 0) = (v, 0) := hzero v
    have h2 : g (0, w) = (φ w, w) := by
      refine Prod.ext ?_ (hsecond w)
      rfl
    have hsum : g (v, w) = g (v, 0) + g (0, w) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    rw [hsum, h1, h2, modelA1Elt_apply]
    simp
  · rintro ⟨φ, rfl⟩
    exact ⟨fun v => by simp [modelA1Elt_apply], fun w => by simp [modelA1Elt_apply]⟩

theorem mem_modelA2_iff (g : SpecialLinearGroup k (VJ × V₀)) :
    g ∈ modelA2 k VJ V₀ ↔ ∃ ψ : VJ →ₗ[k] V₀, modelA2Elt ψ = g := by
  constructor
  · rintro ⟨hzero, hfirst⟩
    let ψ : VJ →ₗ[k] V₀ :=
      (LinearMap.snd k VJ V₀).comp
        ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inl k VJ V₀))
    refine ⟨ψ, ?_⟩
    apply SpecialLinearGroup.ext
    intro p
    obtain ⟨v, w⟩ := p
    have h1 : g (0, w) = (0, w) := hzero w
    have h2 : g (v, 0) = (v, ψ v) := by
      refine Prod.ext (hfirst v) ?_
      rfl
    have hsum : g (v, w) = g (v, 0) + g (0, w) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    rw [hsum, h1, h2, modelA2Elt_apply]
    simp
    abel
  · rintro ⟨ψ, rfl⟩
    exact ⟨fun w => by simp [modelA2Elt_apply], fun v => by simp [modelA2Elt_apply]⟩

private theorem blockSLk_apply_aux (B : SpecialLinearGroup k VJ) (v : VJ) (w : V₀) :
    blockSLk k V₀ B (v, w) = (B v, w) := by
  rfl

theorem modelK1_eq_range : modelK1 k VJ V₀ = (blockSLk (VJ := VJ) k V₀).range := by
  apply le_antisymm
  · intro g hg
    let f : VJ →ₗ[k] VJ :=
      (LinearMap.fst k VJ V₀).comp
        ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inl k VJ V₀))
    let f' : VJ →ₗ[k] VJ :=
      (LinearMap.fst k VJ V₀).comp
        ((SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap.comp (LinearMap.inl k VJ V₀))
    have hg_inv : g⁻¹ ∈ modelK1 k VJ V₀ := (modelK1 k VJ V₀).inv_mem' hg
    have hg_apply (v : VJ) : g (v, 0) = (f v, 0) := by
      refine Prod.ext ?_ (hg.1 v)
      rfl
    have hginv_apply (v : VJ) : g⁻¹ (v, 0) = (f' v, 0) := by
      refine Prod.ext ?_ (hg_inv.1 v)
      rfl
    have hcancel_left (v : VJ) : g⁻¹ (g (v, 0)) = (v, 0) := by
      have h := LinearEquiv.symm_apply_apply (SpecialLinearGroup.toLinearEquiv g) (v, 0)
      simpa [SpecialLinearGroup.toLinearEquiv_symm_apply] using h
    have hcancel_right (v : VJ) : g (g⁻¹ (v, 0)) = (v, 0) := by
      have h := LinearEquiv.apply_symm_apply (SpecialLinearGroup.toLinearEquiv g) (v, 0)
      simpa [SpecialLinearGroup.toLinearEquiv_symm_apply] using h
    have hleft (v : VJ) : f' (f v) = v := by
      calc
        f' (f v) = (g⁻¹ (f v, 0)).1 := rfl
        _ = (g⁻¹ (g (v, 0))).1 := by rw [hg_apply]
        _ = (v, 0).1 := by rw [hcancel_left]
        _ = v := rfl
    have hright (v : VJ) : f (f' v) = v := by
      calc
        f (f' v) = (g (f' v, 0)).1 := rfl
        _ = (g (g⁻¹ (v, 0))).1 := by rw [hginv_apply]
        _ = (v, 0).1 := by rw [hcancel_right]
        _ = v := rfl
    let B : VJ ≃ₗ[k] VJ :=
      LinearEquiv.ofLinearMap f f' (LinearMap.ext hright) (LinearMap.ext hleft)
    have hB_apply (v : VJ) : B v = f v := rfl
    have hg_linear_eq :
        SpecialLinearGroup.toLinearEquiv g =
          (B.prodCongr (LinearEquiv.refl k V₀) : (VJ × V₀) ≃ₗ[k] (VJ × V₀)) := by
      apply LinearEquiv.ext
      intro p
      obtain ⟨v, w⟩ := p
      have hsum : g (v, w) = g (v, 0) + g (0, w) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      change (fun x => (g : VJ × V₀ → VJ × V₀) x) (v, w) =
        (B.prodCongr (LinearEquiv.refl k V₀)) (v, w)
      rw [hsum, hg_apply, hg.2, LinearEquiv.prodCongr_apply]
      exact Prod.ext (by simpa using (hB_apply v).symm) (by simp)
    have hdet_prod :
        LinearEquiv.det (B.prodCongr (LinearEquiv.refl k V₀)) = LinearEquiv.det B * 1 := by
      apply Units.ext
      rw [Units.val_mul, LinearEquiv.coe_det, LinearEquiv.coe_prodCongr,
        LinearMap.det_prodMap]
      simp
    have hgdet : LinearEquiv.det (SpecialLinearGroup.toLinearEquiv g) = 1 := by
      rw [SpecialLinearGroup.toLinearEquiv_eq_coe]
      exact SpecialLinearGroup.det_coe g
    have hdet : LinearEquiv.det B = 1 := by
      have h := congrArg LinearEquiv.det hg_linear_eq
      rw [hgdet] at h
      rw [hdet_prod, mul_one] at h
      exact h.symm
    refine ⟨⟨B, hdet⟩, ?_⟩
    apply SpecialLinearGroup.ext
    intro p
    obtain ⟨v, w⟩ := p
    rw [blockSLk_apply_aux]
    have hsum : g (v, w) = g (v, 0) + g (0, w) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    change ((⟨B, hdet⟩ : SpecialLinearGroup k VJ) v, w) =
      (fun x => (g : VJ × V₀ → VJ × V₀) x) (v, w)
    rw [hsum, hg_apply, hg.2]
    exact Prod.ext (by simpa using hB_apply v) (by simp)
  · rintro g ⟨B, rfl⟩
    constructor
    · intro v
      simpa [blockSLk_apply_aux]
    · intro w
      simpa [blockSLk_apply_aux]

theorem blockSLk_injective : Function.Injective (blockSLk (VJ := VJ) k V₀) := by
  intro B B' h
  apply SpecialLinearGroup.ext
  intro v
  have hv := congrArg (fun g : SpecialLinearGroup k (VJ × V₀) => (g (v, 0)).1) h
  simpa [blockSLk_apply_aux] using hv

theorem blockSLk_apply (B : SpecialLinearGroup k VJ) (v : VJ) (w : V₀) :
    blockSLk k V₀ B (v, w) = (B v, w) := by
  exact blockSLk_apply_aux B v w

theorem blockSLk_mul_modelA1Elt_mul_inv (B : SpecialLinearGroup k VJ) (φ : V₀ →ₗ[k] VJ) :
    blockSLk k V₀ B * modelA1Elt φ * (blockSLk k V₀ B)⁻¹ =
      modelA1Elt ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ) := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  change blockSLk k V₀ B (modelA1Elt φ ((blockSLk k V₀ B)⁻¹ (v, w))) =
    modelA1Elt ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ) (v, w)
  have hinv : (blockSLk k V₀ B)⁻¹ (v, w) = (B⁻¹ v, w) := by
    simpa [map_inv] using blockSLk_apply_aux (B := B⁻¹) v w
  rw [hinv, modelA1Elt_apply, blockSLk_apply_aux, modelA1Elt_apply]
  simp [map_add]

theorem blockSLk_mul_modelA2Elt_mul_inv (B : SpecialLinearGroup k VJ) (ψ : VJ →ₗ[k] V₀) :
    blockSLk k V₀ B * modelA2Elt ψ * (blockSLk k V₀ B)⁻¹ =
      modelA2Elt (ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  change blockSLk k V₀ B (modelA2Elt ψ ((blockSLk k V₀ B)⁻¹ (v, w))) =
    modelA2Elt (ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) (v, w)
  have hinv : (blockSLk k V₀ B)⁻¹ (v, w) = (B⁻¹ v, w) := by
    simpa [map_inv] using blockSLk_apply_aux (B := B⁻¹) v w
  rw [hinv, modelA2Elt_apply, blockSLk_apply_aux, modelA2Elt_apply]
  simp

theorem modelJ_le_modelK1 : modelJ k E VJ V₀ ≤ modelK1 k VJ V₀ := by
  rintro g ⟨B, rfl⟩
  rw [modelK1_eq_range]
  exact ⟨restrictSL (E := E) (VJ := VJ) k B, rfl⟩

theorem modelK1_le_modelP1 : modelK1 k VJ V₀ ≤ modelP1 k VJ V₀ := by
  rintro g ⟨hzero, hone⟩
  exact ⟨hzero, fun w => by rw [hone w]⟩

theorem modelK1_le_modelP2 : modelK1 k VJ V₀ ≤ modelP2 k VJ V₀ := by
  rintro g ⟨hzero, hone⟩
  exact hone

theorem modelA1_le_modelP1 : modelA1 k VJ V₀ ≤ modelP1 k VJ V₀ := by
  rintro g ⟨hfix, hsecond⟩
  exact ⟨fun v => by rw [hfix v], hsecond⟩

theorem modelA2_le_modelP2 : modelA2 k VJ V₀ ≤ modelP2 k VJ V₀ := by
  rintro g ⟨hfix, hfirst⟩
  exact hfix

theorem datumU1_le_modelP1 (e₀ : VJ) :
    datumU1 (modelIota (E := E) k V₀ e₀) ≤ modelP1 k VJ V₀ := by
  rintro g ⟨hsub, hfix⟩
  constructor
  · intro v
    obtain ⟨t, ht⟩ := hsub (v, 0)
    have hg : g (v, 0) = (t • e₀, 0) + (v, 0) := by
      rw [← sub_add_cancel (g (v, 0)) (v, 0), ← ht, modelIota_apply]
    have hsnd := congrArg Prod.snd hg
    simpa using hsnd
  · intro w
    obtain ⟨t, ht⟩ := hsub (0, w)
    have hg : g (0, w) = (t • e₀, 0) + (0, w) := by
      rw [← sub_add_cancel (g (0, w)) (0, w), ← ht, modelIota_apply]
    have hsnd := congrArg Prod.snd hg
    simpa using hsnd

theorem datumU2_le_modelP2 (l₀ : VJ →ₗ[E] E) :
    datumU2 (modelPi k V₀ l₀) ≤ modelP2 k VJ V₀ := by
  rintro g ⟨hsub, hfix⟩
  intro w
  exact hfix (0, w) (by simp [modelPi_apply])

end CFSG.LinearAlgebra.RootGroupSL
