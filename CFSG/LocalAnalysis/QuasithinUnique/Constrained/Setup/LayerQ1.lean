module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensor

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender
open TensorProduct Module

section Conj

variable {F : Type*} [Field F] {M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N]
  [Module F N]

@[expose] def autConj (e : M ≃ₗ[F] N) : (M ≃ₗ[F] M) ≃* (N ≃ₗ[F] N) where
  toFun x := e.symm.trans (x.trans e)
  invFun y := e.trans (y.trans e.symm)
  left_inv x := by
    ext w
    simp
  right_inv y := by
    ext w
    simp
  map_mul' x y := by
    ext w
    simp

theorem autConj_apply (e : M ≃ₗ[F] N) (x : M ≃ₗ[F] M) (w : N) :
    autConj e x w = e (x (e.symm w)) := rfl

theorem autConj_symm_apply (e : M ≃ₗ[F] N) (x : M ≃ₗ[F] M) (w : N) :
    (autConj e x).symm w = e (x.symm (e.symm w)) := rfl

theorem fixGL_map_autConj (e : M ≃ₗ[F] N) (A : Subgroup (M ≃ₗ[F] M)) :
    fixGL (A.map (autConj e).toMonoidHom) = (fixGL A).map (e : M →ₗ[F] N) := by
  ext w
  rw [mem_fixGL, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨e.symm w, ?_, by simp⟩
    intro a ha
    have h1 := h (autConj e a) ⟨a, ha, rfl⟩
    rw [autConj_apply] at h1
    have h2 := congrArg e.symm h1
    simpa using h2
  · rintro ⟨v, hv, rfl⟩ b ⟨a, ha, rfl⟩
    show autConj e a (e v) = e v
    rw [autConj_apply]
    have h3 : a v = v := (mem_fixGL.1 hv) a ha
    simp [h3]

theorem natCard_fixGL_map_autConj (e : M ≃ₗ[F] N) (A : Subgroup (M ≃ₗ[F] M)) :
    Nat.card ↥(fixGL (A.map (autConj e).toMonoidHom)) = Nat.card ↥(fixGL A) := by
  rw [fixGL_map_autConj]
  exact (Nat.card_congr (Submodule.equivMapOfInjective (e : M →ₗ[F] N) e.injective
    (fixGL A)).toEquiv).symm

theorem natCard_map_autConj (e : M ≃ₗ[F] N) (A : Subgroup (M ≃ₗ[F] M)) :
    Nat.card ↥(A.map (autConj e).toMonoidHom) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (autConj e).injective

theorem natCard_le_weight_map_autConj (e : M ≃ₗ[F] N) (A : Subgroup (M ≃ₗ[F] M))
    (h : Nat.card M ≤ Nat.card ↥A * Nat.card ↥(fixGL A)) :
    Nat.card N ≤ Nat.card ↥(A.map (autConj e).toMonoidHom) *
      Nat.card ↥(fixGL (A.map (autConj e).toMonoidHom)) := by
  rw [natCard_map_autConj, natCard_fixGL_map_autConj, ← Nat.card_congr e.toEquiv]
  exact h

end Conj

section Tensor

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {V V' : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)] [∀ i, AddCommGroup (V' i)]
  [∀ i, Module F (V' i)]

theorem congr_factorEnd_het (τ : ∀ i, V i ≃ₗ[F] V' i) (i : ι) (f : Module.End F (V i)) :
    (PiTensorProduct.congr τ).toLinearMap ∘ₗ factorEnd i f ∘ₗ
        (PiTensorProduct.congr τ).symm.toLinearMap =
      factorEnd i ((τ i).toLinearMap ∘ₗ f ∘ₗ (τ i).symm.toLinearMap) := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun m => ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    PiTensorProduct.congr_symm_tprod, factorEnd_tprod, PiTensorProduct.congr_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

end Tensor

end CFSG.QuasithinUnique.Setup.Layer
