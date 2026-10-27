module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv

variable (k : Type) [Field k]

section Tangent

variable (A : Type) [CommRing A] [Algebra k A]

@[expose] def tangentSpace (x : A →ₐ[k] k) : Submodule k (A →ₗ[k] k) where
  carrier := {D | ∀ a b, D (a * b) = x a * D b + x b * D a}
  add_mem' {D E} hD hE a b := by
    simp only [Set.mem_ofPred_eq] at hD hE ⊢
    simp only [LinearMap.add_apply, hD a b, hE a b]
    ring
  zero_mem' a b := by simp
  smul_mem' c D hD a b := by
    simp only [Set.mem_ofPred_eq] at hD ⊢
    simp only [LinearMap.smul_apply, hD a b, smul_eq_mul]
    ring

abbrev TangentSpace (x : A →ₐ[k] k) : Type := ↥(tangentSpace k A x)

instance (x : A →ₐ[k] k) : AddCommGroup (TangentSpace k A x) :=
  inferInstanceAs (AddCommGroup ↥(tangentSpace k A x))

instance (x : A →ₐ[k] k) : Module k (TangentSpace k A x) :=
  inferInstanceAs (Module k ↥(tangentSpace k A x))

variable {k A}

theorem mem_tangentSpace {x : A →ₐ[k] k} {D : A →ₗ[k] k} :
    D ∈ tangentSpace k A x ↔ ∀ a b, D (a * b) = x a * D b + x b * D a :=
  Iff.rfl

theorem map_one_of_mem_tangentSpace {x : A →ₐ[k] k} {D : A →ₗ[k] k}
    (hD : D ∈ tangentSpace k A x) : D 1 = 0 := by
  have h := hD 1 1
  simp only [mul_one, map_one, one_mul] at h
  linear_combination -h

variable {B C : Type} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]

@[expose] def tangentMap (φ : B →ₐ[k] A) {x : A →ₐ[k] k} {y : B →ₐ[k] k} (h : x.comp φ = y) :
    TangentSpace k A x →ₗ[k] TangentSpace k B y where
  toFun D := ⟨D.1 ∘ₗ φ.toLinearMap, fun a b => by
    have hD : ∀ a b, D.1 (a * b) = x a * D.1 b + x b * D.1 a := D.2
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
    rw [hD, ← h]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_tangentMap (φ : B →ₐ[k] A) {x : A →ₐ[k] k} {y : B →ₐ[k] k} (h : x.comp φ = y)
    (D : TangentSpace k A x) :
    ((tangentMap φ h D : tangentSpace k B y) : B →ₗ[k] k) = (D : A →ₗ[k] k) ∘ₗ φ.toLinearMap :=
  rfl

theorem tangentMap_comp (φ : B →ₐ[k] A) (ψ : C →ₐ[k] B) {x : A →ₐ[k] k} {y : B →ₐ[k] k}
    {z : C →ₐ[k] k} (h : x.comp φ = y) (h' : y.comp ψ = z) :
    tangentMap (φ.comp ψ) (by rw [← h', ← h, AlgHom.comp_assoc]) =
      (tangentMap ψ h').comp (tangentMap φ h) :=
  rfl

theorem tangentMap_id {x : A →ₐ[k] k} :
    tangentMap (AlgHom.id k A) (x := x) (AlgHom.comp_id x) = LinearMap.id :=
  rfl

theorem tangentMap_pow (φ : A →ₐ[k] A) {x : A →ₐ[k] k} (h : x.comp φ = x) (n : ℕ) :
    ∃ hn : x.comp (φ ^ n) = x, tangentMap φ h ^ n = tangentMap (φ ^ n) hn := by
  induction n with
  | zero => exact ⟨AlgHom.comp_id x, rfl⟩
  | succ n ih =>
    obtain ⟨hn, e⟩ := ih
    refine ⟨?_, ?_⟩
    · show x.comp ((φ ^ n).comp φ) = x
      rw [← AlgHom.comp_assoc, hn, h]
    · rw [pow_succ', e]
      rfl

end Tangent

section Hopf

variable {k} {A : Type} [CommRing A] [HopfAlgebra k A]

theorem tangent_convMul {D : A →ₗ[k] k} (hD : D ∈ tangentSpace k A (counitAlgHom k A))
    (f g : A →ₐ[k] A) (hf : (counitAlgHom k A).comp f = counitAlgHom k A)
    (hg : (counitAlgHom k A).comp g = counitAlgHom k A) :
    D ∘ₗ (toConv f * toConv g).ofConv.toLinearMap = D ∘ₗ f.toLinearMap + D ∘ₗ g.toLinearMap := by
  have h1 : (toConv f * toConv g).ofConv.toLinearMap =
      LinearMap.mul' k A ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ comul := by
    have := AlgHom.toLinearMap_convMul (toConv f) (toConv g)
    rw [LinearMap.convMul_def] at this
    exact congrArg ofConv this
  have hfε : ∀ a, counit (R := k) (f a) = counit a := fun a => by
    have := congrArg (fun φ : A →ₐ[k] k => φ a) hf
    simpa using this
  have hgε : ∀ a, counit (R := k) (g a) = counit a := fun a => by
    have := congrArg (fun φ : A →ₐ[k] k => φ a) hg
    simpa using this
  have h2 : D ∘ₗ LinearMap.mul' k A ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap =
      LinearMap.mul' k k ∘ₗ TensorProduct.map (D ∘ₗ f.toLinearMap) counit +
        LinearMap.mul' k k ∘ₗ TensorProduct.map counit (D ∘ₗ g.toLinearMap) := by
    refine TensorProduct.ext' fun a b => ?_
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply, LinearMap.add_apply]
    rw [hD (f a) (g b)]
    simp only [counitAlgHom_apply, hfε, hgε]
    ring
  have h3 : ∀ u v : A →ₗ[k] k, LinearMap.mul' k k ∘ₗ TensorProduct.map u v ∘ₗ comul =
      (toConv u * toConv v).ofConv := fun u v => rfl
  have hone : (counit : A →ₗ[k] k) = (1 : WithConv (A →ₗ[k] k)).ofConv := by
    rw [LinearMap.convOne_def]
    ext a
    simp
  rw [h1]
  change (D ∘ₗ LinearMap.mul' k A ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap) ∘ₗ comul = _
  rw [h2, LinearMap.add_comp, LinearMap.comp_assoc, LinearMap.comp_assoc, h3, h3, hone]
  simp

theorem tangent_convOne {D : A →ₗ[k] k} (hD : D ∈ tangentSpace k A (counitAlgHom k A)) :
    D ∘ₗ (1 : WithConv (A →ₐ[k] A)).ofConv.toLinearMap = 0 := by
  ext a
  rw [AlgHom.convOne_def, ofConv_toConv]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    LinearMap.zero_apply]
  rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, map_smul,
    map_one_of_mem_tangentSpace hD, smul_zero]

theorem tangent_convInv {D : A →ₗ[k] k} (hD : D ∈ tangentSpace k A (counitAlgHom k A))
    (f : A →ₐ[k] A) (hf : (counitAlgHom k A).comp f = counitAlgHom k A) :
    D ∘ₗ (toConv f)⁻¹.ofConv.toLinearMap = -(D ∘ₗ f.toLinearMap) := by
  have hinv : (counitAlgHom k A).comp (toConv f)⁻¹.ofConv = counitAlgHom k A := by
    change (counitAlgHom k A).comp (f.comp (antipodeAlgHom k A)) = _
    rw [← AlgHom.comp_assoc, hf, AlgHom.counitAlgHom_comp_antipodeAlgHom]
  have h := tangent_convMul hD f (toConv f)⁻¹.ofConv hf hinv
  rw [toConv_ofConv, mul_inv_cancel, tangent_convOne hD] at h
  rw [eq_neg_iff_add_eq_zero, add_comm, ← h]

end Hopf

end CFSG.LieType.AlgebraicGroups
