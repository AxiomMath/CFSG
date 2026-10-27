module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module

section Restrict

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (U : Submodule (ZMod 2) W)

@[expose] noncomputable def restrictU (g : W ≃ₗ[ZMod 2] W) (hU : ∀ u ∈ U, g u ∈ U)
    (hUi : ∀ u ∈ U, g.symm u ∈ U) : U ≃ₗ[ZMod 2] U :=
  LinearEquiv.ofSubmodules g U U (le_antisymm (Submodule.map_le_iff_le_comap.2 fun u hu => hU u hu)
    (fun u hu => ⟨g.symm u, hUi u hu, by simp⟩))

theorem restrictU_apply (g : W ≃ₗ[ZMod 2] W) (hU : ∀ u ∈ U, g u ∈ U)
    (hUi : ∀ u ∈ U, g.symm u ∈ U) (u : U) :
    ((restrictU U g hU hUi u : U) : W) = g u :=
  LinearEquiv.ofSubmodules_apply _ _ _

theorem restrictU_symm_apply (g : W ≃ₗ[ZMod 2] W) (hU : ∀ u ∈ U, g u ∈ U)
    (hUi : ∀ u ∈ U, g.symm u ∈ U) (u : U) :
    ((((restrictU U g hU hUi).symm u : U) : W)) = g.symm u := by
  apply g.injective
  rw [LinearEquiv.apply_symm_apply, ← restrictU_apply U g hU hUi, LinearEquiv.apply_symm_apply]


end Restrict

section Ext

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable (U Wc : Submodule (ZMod 2) W) (hc : IsCompl U Wc)
include hc

@[expose] noncomputable def extFun (φ : U ≃ₗ[ZMod 2] U) : W ≃ₗ[ZMod 2] W :=
  (Submodule.prodEquivOfIsCompl U Wc hc).symm.trans
    ((φ.prodCongr (LinearEquiv.refl (ZMod 2) Wc)).trans (Submodule.prodEquivOfIsCompl U Wc hc))

theorem exists_decomp_compl (v : W) : ∃ (u : U) (w : Wc), v = (u : W) + (w : W) := by
  have h : v ∈ U ⊔ Wc := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

theorem extFun_apply (φ : U ≃ₗ[ZMod 2] U) (u : U) (w : Wc) :
    extFun U Wc hc φ ((u : W) + (w : W)) = (φ u : W) + (w : W) := by
  have hs : (Submodule.prodEquivOfIsCompl U Wc hc).symm ((u : W) + (w : W)) = (u, w) :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  simp only [extFun, LinearEquiv.trans_apply, hs, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl']

theorem extFun_one : extFun U Wc hc (1 : U ≃ₗ[ZMod 2] U) = 1 := by
  ext v
  obtain ⟨u, w, rfl⟩ := exists_decomp_compl U Wc hc v
  rw [extFun_apply]
  simp

theorem extFun_mul (φ ψ : U ≃ₗ[ZMod 2] U) :
    extFun U Wc hc (φ * ψ) = extFun U Wc hc φ * extFun U Wc hc ψ := by
  ext v
  obtain ⟨u, w, rfl⟩ := exists_decomp_compl U Wc hc v
  show extFun U Wc hc (φ * ψ) (u + w) = extFun U Wc hc φ (extFun U Wc hc ψ (u + w))
  rw [extFun_apply, extFun_apply, extFun_apply]
  rfl

@[expose] noncomputable def extEquiv : (U ≃ₗ[ZMod 2] U) →* (W ≃ₗ[ZMod 2] W) where
  toFun := extFun U Wc hc
  map_one' := extFun_one U Wc hc
  map_mul' := extFun_mul U Wc hc

theorem extEquiv_apply (φ : U ≃ₗ[ZMod 2] U) (u : U) (w : Wc) :
    extEquiv U Wc hc φ ((u : W) + (w : W)) = (φ u : W) + (w : W) :=
  extFun_apply U Wc hc φ u w

theorem extEquiv_injective : Function.Injective (extEquiv U Wc hc) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have key : ∀ u : U, (φ u : W) = (u : W) := by
    intro u
    have h := extEquiv_apply U Wc hc φ u 0
    rw [show extEquiv U Wc hc φ = 1 from hφ] at h
    simpa using h.symm
  exact LinearEquiv.ext (fun u => Subtype.ext (key u))

theorem extFun_on_U (φ : U ≃ₗ[ZMod 2] U) (u : U) :
    extFun U Wc hc φ (u : W) = ((φ u : U) : W) := by
  have h := extFun_apply U Wc hc φ u 0
  simpa using h

theorem extFun_on_Wc (φ : U ≃ₗ[ZMod 2] U) (w : Wc) :
    extFun U Wc hc φ (w : W) = (w : W) := by
  have h := extFun_apply U Wc hc φ 0 w
  simpa using h

theorem conj_extFun (g : W ≃ₗ[ZMod 2] W) (hU : ∀ u ∈ U, g u ∈ U)
    (hUi : ∀ u ∈ U, g.symm u ∈ U) (hW : ∀ w ∈ Wc, g w ∈ Wc) (hWi : ∀ w ∈ Wc, g.symm w ∈ Wc)
    (φ : U ≃ₗ[ZMod 2] U) :
    g * extFun U Wc hc φ * g.symm =
      extFun U Wc hc (restrictU U g hU hUi * φ * (restrictU U g hU hUi).symm) := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, w, rfl⟩ := exists_decomp_compl U Wc hc v
  have hsplit : g.symm ((u : W) + (w : W)) = (g.symm u : W) + (g.symm w : W) := map_add _ _ _
  have hsymu : g.symm (u : W) = ((restrictU U g hU hUi).symm u : W) :=
    (restrictU_symm_apply U g hU hUi u).symm
  have hwW : g.symm (w : W) ∈ Wc := hWi w w.2
  have hw' : extFun U Wc hc φ (g.symm (w : W)) = g.symm (w : W) :=
    extFun_on_Wc U Wc hc φ ⟨g.symm w, hwW⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsplit, map_add, map_add, hsymu,
    extFun_on_U, hw', LinearEquiv.apply_symm_apply, ← restrictU_apply U g hU hUi]
  rw [extFun_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]

end Ext

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
