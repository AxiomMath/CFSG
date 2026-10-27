module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LocalAnalysis.ComponentClassification.ElementaryAbelianModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open Subgroup

theorem mulAut_eq_top_of_transvection_mem {E : Type*} [Group E] [Finite E]
    (hE : ∀ x y : E, x * y = y * x) (h2 : ∀ x : E, x * x = 1) (H : Subgroup (MulAut E))
    (hH : ∀ (σ : MulAut E) (c : E), (∀ x : E, x⁻¹ * σ x ∈ zpowers c) → σ ∈ H) : H = ⊤ := by
  let : CommGroup E := { ‹Group E› with mul_comm := hE }
  let : Module (ZMod 2) (Additive E) :=
    ElementaryAbelianModule.moduleStructure 2 fun x => by rw [pow_two]; exact h2 x
  have : Finite (Additive E) := inferInstanceAs (Finite E)
  have : FiniteDimensional (ZMod 2) (Additive E) := Module.Finite.of_finite
  let ρ : (Additive E ≃ₗ[ZMod 2] Additive E) →* MulAut E :=
    { toFun := fun e => MulEquiv.toAdditive.symm e.toAddEquiv
      map_one' := MulEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl }
  have htr : LinearEquiv.transvections (ZMod 2) (Additive E) ⊆ H.comap ρ := by
    rintro _ ⟨f, v, hfv, rfl⟩
    refine hH _ (Additive.toMul v) fun x => ?_
    change x⁻¹ * Additive.toMul (LinearEquiv.transvection hfv (Additive.ofMul x)) ∈ _
    rw [LinearEquiv.transvection.apply, toMul_add, toMul_ofMul, inv_mul_cancel_left]
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one (f (Additive.ofMul x))
      with h | h
    · rw [h, zero_smul, toMul_zero]
      exact one_mem _
    · rw [h, one_smul]
      exact mem_zpowers _
  have htop : H.comap ρ = ⊤ := by
    rw [eq_top_iff, ← CFSG.GroupTheory.GLnTwoSplitting.closure_transvections_eq_top,
      closure_le]
    exact htr
  refine eq_top_iff.mpr fun σ _ => ?_
  have hσ : ρ (ElementaryAbelianModule.linearAutomorphism 2 σ) = σ := MulEquiv.ext fun _ => rfl
  have hmem : ElementaryAbelianModule.linearAutomorphism 2 σ ∈ H.comap ρ := by
    rw [htop]
    exact mem_top _
  rwa [mem_comap, hσ] at hmem

end CFSG.ComponentClassification.GrSLit.GrS4
