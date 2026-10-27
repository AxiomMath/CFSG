module

public import CFSG.LocalAnalysis.ComponentInitial.LinearSummandCentralizer
public import Mathlib.LinearAlgebra.Determinant

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped MatrixGroups

namespace ProjectiveEigenspace

variable {k : Type*} [Field k] {n : ℕ}

@[expose] def summandSpecialLinear (A W : Submodule k (Fin n → k)) : Set (GL (Fin n) k) :=
  {g | (∀ w ∈ W, (g : Matrix (Fin n) (Fin n) k) *ᵥ w = w) ∧
    ∃ hA : ∀ a ∈ A, (g : Matrix (Fin n) (Fin n) k) *ᵥ a ∈ A,
      LinearMap.det ((mulVecLin (g : Matrix (Fin n) (Fin n) k)).restrict hA) = 1}

variable {M : Type*} [AddCommGroup M] [Module k M]

@[expose] def transportEnd (Ψ : M ≃ₗ[k] (Fin n → k)) :
    Matrix (Fin n) (Fin n) k →* Module.End k M where
  toFun A := Ψ.symm.toLinearMap ∘ₗ mulVecLin A ∘ₗ Ψ.toLinearMap
  map_one' := by
    ext x
    simp
  map_mul' A B := by
    ext x
    simp [mulVec_mulVec]

@[expose] def transportGL (Ψ : M ≃ₗ[k] (Fin n → k)) :
    GL (Fin n) k →* LinearMap.GeneralLinearGroup k M :=
  Units.map (transportEnd Ψ)

theorem transportGL_apply (Ψ : M ≃ₗ[k] (Fin n → k)) (g : GL (Fin n) k) (x : M) :
    ((transportGL Ψ g : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) x =
      Ψ.symm ((g : Matrix (Fin n) (Fin n) k) *ᵥ Ψ x) := rfl

theorem apply_eq_of_isPerfect_of_le_centralizer_transport {E W : Type*} [Field E] [Algebra k E]
    [AddCommGroup W] [Module k W] {m : ℕ} (hm : 2 ≤ m) (Ψ : ((Fin m → E) × W) ≃ₗ[k] (Fin n → k))
    {S R : Subgroup (GL (Fin n) k)}
    (hS : ∀ s : SpecialLinearGroup (Fin m) E, ∃ g ∈ S, ∀ x,
      (g : Matrix (Fin n) (Fin n) k) *ᵥ Ψ x =
        Ψ ((summandSL k E W m s : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x))
    (hR : R ≤ Subgroup.centralizer (S : Set (GL (Fin n) k))) (hRp : ⁅R, R⁆ = R)
    {g : GL (Fin n) k} (hg : g ∈ R) (v : Fin m → E) :
    (g : Matrix (Fin n) (Fin n) k) *ᵥ Ψ (v, 0) = Ψ (v, 0) := by
  have hρS : ∀ s, ∃ g ∈ S, transportGL Ψ g = summandSL k E W m s := fun s => by
    obtain ⟨g, hgS, hg⟩ := hS s
    refine ⟨g, hgS, Units.ext (LinearMap.ext fun x => ?_)⟩
    change Ψ.symm ((g : Matrix (Fin n) (Fin n) k) *ᵥ Ψ x) = _
    rw [hg, LinearEquiv.symm_apply_apply]
  have hR' : R.map (transportGL Ψ) ≤
      Subgroup.centralizer ((summandSL k E W m).range : Set _) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    obtain ⟨g, hgS, hgs⟩ := hρS s
    rw [← hgs, ← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hR hr)) g hgS]
  have hRp' : Group.IsPerfect (R.map (transportGL Ψ)) :=
    Subgroup.isPerfect_iff.2 (by rw [← Subgroup.map_commutator, hRp])
  have hfix := (natural_special_linear_summand_centralizer k E W m hm).2.2 _ hR' hRp'
    (transportGL Ψ g) (Subgroup.mem_map_of_mem _ hg) v
  have h2 := congrArg Ψ hfix
  rwa [transportGL_apply, LinearEquiv.apply_symm_apply] at h2

end ProjectiveEigenspace

end CFSG.LocalAnalysis.ComponentInitial
