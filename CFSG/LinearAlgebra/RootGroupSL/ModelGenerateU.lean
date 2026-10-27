module

public import CFSG.LinearAlgebra.RootGroupSL.ModelGenerate
public import CFSG.LinearAlgebra.RootGroupSL.ModelPDecomp

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k] [Finite E] [CharP k 2]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma blockSLk_transvecSL_apply {w : VJ} {f : VJ →ₗ[k] k} (hf : f w = 0)
    (v : VJ) (w' : V₀) :
    blockSLk k V₀ (transvecSL w f) (v, w') = (v + f v • w, w') := by
  rw [blockSLk_apply, transvecSL_apply hf]

private lemma trace_comp_restrictScalars_apply_eq_zero {l : VJ →ₗ[E] E} {w : VJ}
    (h : l w = 0) : ((Algebra.trace k E).comp (l.restrictScalars k)) w = 0 := by
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, h, map_zero]

theorem modelA1Elt_smulRight_mem_datumU1 (e₀ : VJ) (f : V₀ →ₗ[k] k) :
    modelA1Elt (f.smulRight e₀) ∈ datumU1 (modelIota (E := E) k V₀ e₀) := by
  constructor
  · intro x
    obtain ⟨v, w⟩ := x
    refine ⟨algebraMap k E (f w), ?_⟩
    have hx : modelA1Elt (f.smulRight e₀) (v, w) - (v, w) = (f w • e₀, 0) := by
      rw [modelA1Elt_apply, LinearMap.smulRight_apply]
      ext <;> simp
    rw [modelIota_apply, IsScalarTower.algebraMap_smul (A := E) (f w) e₀]
    exact hx.symm
  · intro t
    have hx : modelA1Elt (f.smulRight e₀) (t • e₀, 0) = (t • e₀, 0) := by
      rw [modelA1Elt_apply, LinearMap.smulRight_apply, map_zero, zero_smul, add_zero]
    rw [modelIota_apply]
    exact hx

theorem blockSLk_transvecSL_mem_datumU1 (e₀ : VJ) {l : VJ →ₗ[E] E} (h : l e₀ = 0) :
    blockSLk k V₀ (transvecSL e₀ ((Algebra.trace k E).comp (l.restrictScalars k))) ∈
      datumU1 (modelIota (E := E) k V₀ e₀) := by
  have hf := trace_comp_restrictScalars_apply_eq_zero (k := k) h
  constructor
  · intro x
    obtain ⟨v, w⟩ := x
    refine ⟨algebraMap k E ((Algebra.trace k E) (l v)), ?_⟩
    have hx : blockSLk k V₀
        (transvecSL e₀ ((Algebra.trace k E).comp (l.restrictScalars k))) (v, w) - (v, w) =
        ((Algebra.trace k E) (l v) • e₀, 0) := by
      rw [blockSLk_transvecSL_apply hf]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      ext <;> simp
    rw [modelIota_apply,
      IsScalarTower.algebraMap_smul (A := E) ((Algebra.trace k E) (l v)) e₀]
    exact hx.symm
  · intro t
    have ht : l (t • e₀) = 0 := by rw [map_smul, h, smul_zero]
    have hx : blockSLk k V₀
        (transvecSL e₀ ((Algebra.trace k E).comp (l.restrictScalars k))) (t • e₀, 0) =
        (t • e₀, 0) := by
      rw [blockSLk_transvecSL_apply hf, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        ht, map_zero, zero_smul, add_zero]
    rw [modelIota_apply]
    exact hx

theorem modelA2Elt_smulRight_mem_datumU2 (l₀ : VJ →ₗ[E] E) (w : V₀) :
    modelA2Elt (((Algebra.trace k E).comp (l₀.restrictScalars k)).smulRight w) ∈
      datumU2 (modelPi k V₀ l₀) := by
  constructor
  · intro x
    obtain ⟨v, w'⟩ := x
    have hpair : modelA2Elt (((Algebra.trace k E).comp (l₀.restrictScalars k)).smulRight w)
        (v, w') - (v, w') = (0, (Algebra.trace k E) (l₀ v) • w) := by
      rw [modelA2Elt_apply, LinearMap.smulRight_apply]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      ext <;> simp
    rw [hpair, modelPi_apply, map_zero]
  · intro x hx
    obtain ⟨v, w'⟩ := x
    have hv : l₀ v = 0 := by simpa [modelPi_apply] using hx
    rw [modelA2Elt_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, hv, map_zero, zero_smul, add_zero]

theorem blockSLk_transvecSL_mem_datumU2 (l₀ : VJ →ₗ[E] E) {w : VJ} (h : l₀ w = 0) :
    blockSLk k V₀ (transvecSL w ((Algebra.trace k E).comp (l₀.restrictScalars k))) ∈
      datumU2 (modelPi k V₀ l₀) := by
  have hf := trace_comp_restrictScalars_apply_eq_zero (k := k) h
  constructor
  · intro x
    obtain ⟨v, w'⟩ := x
    have hpair : blockSLk k V₀
        (transvecSL w ((Algebra.trace k E).comp (l₀.restrictScalars k))) (v, w') - (v, w') =
        ((Algebra.trace k E) (l₀ v) • w, 0) := by
      rw [blockSLk_transvecSL_apply hf]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      ext <;> simp
    rw [hpair, modelPi_apply]
    have hmap : l₀ ((Algebra.trace k E) (l₀ v) • w) =
        (Algebra.trace k E) (l₀ v) • l₀ w :=
      map_smul (l₀.restrictScalars k) _ _
    rw [hmap, h, smul_zero]
  · intro x hx
    obtain ⟨v, w'⟩ := x
    have hv : l₀ v = 0 := by simpa [modelPi_apply] using hx
    rw [blockSLk_transvecSL_apply hf, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      hv, map_zero, zero_smul, add_zero]

theorem modelJ_sup_datumU1 (hm : 3 ≤ Module.finrank E VJ) {e₀ : VJ} (he : e₀ ≠ 0) :
    modelJ k E VJ V₀ ⊔ datumU1 (modelIota (E := E) k V₀ e₀) = modelP1 k VJ V₀ := by
  apply le_antisymm
  · exact sup_le (modelJ_le_modelK1.trans modelK1_le_modelP1) (datumU1_le_modelP1 e₀)
  · obtain ⟨l₀, hl₀, hl₀e⟩ :=
      exists_dual_ne_zero_apply_eq_zero (E := E) (V := VJ) (by omega) e₀
    have hJ : modelJ k E VJ V₀ ≤
        modelJ k E VJ V₀ ⊔ datumU1 (modelIota (E := E) k V₀ e₀) := le_sup_left
    have hbaseK : blockSLk k V₀
        (transvecSL e₀ ((Algebra.trace k E).comp (l₀.restrictScalars k))) ∈
        modelJ k E VJ V₀ ⊔ datumU1 (modelIota (E := E) k V₀ e₀) :=
      Subgroup.mem_sup_right (blockSLk_transvecSL_mem_datumU1 (E := E) e₀ hl₀e)
    have hK1 : modelK1 k VJ V₀ ≤
        modelJ k E VJ V₀ ⊔ datumU1 (modelIota (E := E) k V₀ e₀) :=
      modelK1_le_of_transvec hm _ hJ he hl₀ hl₀e hbaseK
    have hA1base : ∀ f : V₀ →ₗ[k] k, modelA1Elt (f.smulRight e₀) ∈
        modelJ k E VJ V₀ ⊔ datumU1 (modelIota (E := E) k V₀ e₀) :=
      fun f => Subgroup.mem_sup_right (modelA1Elt_smulRight_mem_datumU1 (E := E) e₀ f)
    have hA1 : modelA1 k VJ V₀ ≤
        modelJ k E VJ V₀ ⊔ datumU1 (modelIota (E := E) k V₀ e₀) :=
      modelA1_le_of_mem (by omega) _ hJ he hA1base
    calc modelP1 k VJ V₀ = modelA1 k VJ V₀ ⊔ modelK1 k VJ V₀ :=
          (modelA1_sup_modelK1 (k := k) (VJ := VJ) (V₀ := V₀)).symm
      _ ≤ modelJ k E VJ V₀ ⊔ datumU1 (modelIota (E := E) k V₀ e₀) := sup_le hA1 hK1

theorem modelJ_sup_datumU2 (hm : 3 ≤ Module.finrank E VJ) {l₀ : VJ →ₗ[E] E} (hl : l₀ ≠ 0) :
    modelJ k E VJ V₀ ⊔ datumU2 (modelPi k V₀ l₀) = modelP2 k VJ V₀ := by
  apply le_antisymm
  · exact sup_le (modelJ_le_modelK1.trans modelK1_le_modelP2) (datumU2_le_modelP2 l₀)
  · obtain ⟨w₀, hw₀, hlw⟩ :=
      exists_ne_zero_apply_eq_zero (E := E) (V := VJ) (by omega) l₀
    have hJ : modelJ k E VJ V₀ ≤ modelJ k E VJ V₀ ⊔ datumU2 (modelPi k V₀ l₀) :=
      le_sup_left
    have hbaseK : blockSLk k V₀
        (transvecSL w₀ ((Algebra.trace k E).comp (l₀.restrictScalars k))) ∈
        modelJ k E VJ V₀ ⊔ datumU2 (modelPi k V₀ l₀) :=
      Subgroup.mem_sup_right (blockSLk_transvecSL_mem_datumU2 (E := E) l₀ hlw)
    have hK1 : modelK1 k VJ V₀ ≤ modelJ k E VJ V₀ ⊔ datumU2 (modelPi k V₀ l₀) :=
      modelK1_le_of_transvec hm _ hJ hw₀ hl hlw hbaseK
    have hA2base : ∀ w : V₀, modelA2Elt
        (((Algebra.trace k E).comp (l₀.restrictScalars k)).smulRight w) ∈
        modelJ k E VJ V₀ ⊔ datumU2 (modelPi k V₀ l₀) :=
      fun w => Subgroup.mem_sup_right (modelA2Elt_smulRight_mem_datumU2 (E := E) l₀ w)
    have hA2 : modelA2 k VJ V₀ ≤ modelJ k E VJ V₀ ⊔ datumU2 (modelPi k V₀ l₀) :=
      modelA2_le_of_mem (by omega) _ hJ hl hA2base
    calc modelP2 k VJ V₀ = modelA2 k VJ V₀ ⊔ modelK1 k VJ V₀ :=
          (modelA2_sup_modelK1 (k := k) (VJ := VJ) (V₀ := V₀)).symm
      _ ≤ modelJ k E VJ V₀ ⊔ datumU2 (modelPi k V₀ l₀) := sup_le hA2 hK1

end CFSG.LinearAlgebra.RootGroupSL
