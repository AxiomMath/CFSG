module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

@[expose] def ratClosure (Ψ : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ) :=
  {β | IsRoot τ β ∧ (fun k => (β k : ℚ)) ∈
    Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ)}

theorem mem_ratClosure {Ψ : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} :
    β ∈ ratClosure Ψ ↔ IsRoot τ β ∧ (fun k => (β k : ℚ)) ∈
      Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ) :=
  Iff.rfl

private theorem toRat_add (x y : Fin τ.rank → ℤ) :
    (fun k => ((x + y) k : ℚ)) = (fun k => (x k : ℚ)) + fun k => (y k : ℚ) := by
  funext k
  simp

private theorem toRat_zsmul (c : ℤ) (x : Fin τ.rank → ℤ) :
    (fun k => ((c • x) k : ℚ)) = (c : ℚ) • fun k => (x k : ℚ) := by
  funext k
  simp

private theorem toRat_neg (x : Fin τ.rank → ℤ) :
    (fun k => ((-x) k : ℚ)) = -fun k => (x k : ℚ) := by
  funext k
  simp

theorem subset_ratClosure {Ψ : Set (Fin τ.rank → ℤ)} (h : ∀ α ∈ Ψ, IsRoot τ α) :
    Ψ ⊆ ratClosure Ψ := fun α hα =>
  ⟨h α hα, Submodule.subset_span ⟨α, hα, rfl⟩⟩

theorem span_ratClosure {Ψ : Set (Fin τ.rank → ℤ)} (h : ∀ α ∈ Ψ, IsRoot τ α) :
    Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' ratClosure Ψ) =
      Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono
    (Set.image_mono (subset_ratClosure h)))
  rintro _ ⟨β, hβ, rfl⟩
  exact hβ.2

@[expose] noncomputable def ratForm (τ : Tag) :
    (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ) →ₗ[ℚ] ℚ :=
  Matrix.toLinearMap₂' ℚ (τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ))

theorem ratForm_toRat (x y : Fin τ.rank → ℤ) :
    ratForm τ (fun k => (x k : ℚ)) (fun k => (y k : ℚ)) = iform x y := by
  rw [ratForm, Matrix.toLinearMap₂'_apply', iform]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem iform_eq_zero_of_mem_ratClosure {Ψ : Set (Fin τ.rank → ℤ)} {α β : Fin τ.rank → ℤ}
    (hα : ∀ ψ ∈ Ψ, iform α ψ = 0) (hβ : β ∈ ratClosure Ψ) : iform α β = 0 := by
  have hle : Submodule.span ℚ ((fun γ (k : Fin τ.rank) => (γ k : ℚ)) '' Ψ) ≤
      LinearMap.ker (ratForm τ (fun k => (α k : ℚ))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ψ, hψ, rfl⟩
    change ratForm τ (fun k => (α k : ℚ)) (fun k => (ψ k : ℚ)) = 0
    rw [ratForm_toRat, hα ψ hψ, Int.cast_zero]
  have h : ratForm τ (fun k => (α k : ℚ)) (fun k => (β k : ℚ)) = 0 := hle hβ.2
  rw [ratForm_toRat] at h
  exact_mod_cast h


theorem irreducible_of_subset_ratClosure {Ψ X : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hΨX : Ψ ⊆ X) (hX : X ⊆ ratClosure Ψ) (S : Set (Fin τ.rank → ℤ)) (hS : S ⊆ X)
    (hperp : ∀ α ∈ S, ∀ β ∈ X, β ∉ S → iform α β = 0) : S = ∅ ∨ S = X := by
  have h0 := hΨ.irreducible (S ∩ Ψ) Set.inter_subset_right fun α hα β hβ hβS =>
    hperp α hα.1 β (hΨX hβ) fun h => hβS ⟨h, hβ⟩
  rcases h0 with h0 | h0
  ·
    left
    refine Set.eq_empty_of_forall_notMem fun α hα => ?_
    have hαΨ : ∀ ψ ∈ Ψ, iform α ψ = 0 := fun ψ hψ =>
      hperp α hα ψ (hΨX hψ) fun h => (Set.eq_empty_iff_forall_notMem.1 h0) ψ ⟨h, hψ⟩
    have := iform_eq_zero_of_mem_ratClosure hαΨ (hX (hS hα))
    exact (iform_self_pos_of_isRoot (hX (hS hα)).1).ne' this
  ·
    right
    refine Set.Subset.antisymm hS fun β hβ => ?_
    by_contra hβS
    have hβΨ : ∀ ψ ∈ Ψ, iform β ψ = 0 := fun ψ hψ => by
      have hψS : ψ ∈ S := (h0.symm ▸ hψ : ψ ∈ S ∩ Ψ).1
      rw [iform_comm]
      exact hperp ψ hψS β hβ hβS
    have := iform_eq_zero_of_mem_ratClosure hβΨ (hX hβ)
    exact (iform_self_pos_of_isRoot (hX hβ).1).ne' this

theorem isRootComponent_ratClosure {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    IsRootComponent (ratClosure Ψ) where
  isRoot α hα := hα.1
  neg_mem α hα := by
    refine ⟨IsRoot.neg hα.1, ?_⟩
    rw [toRat_neg]
    exact Submodule.neg_mem _ hα.2
  add_mem α hα β hβ hr := by
    refine ⟨hr, ?_⟩
    rw [toRat_add]
    exact Submodule.add_mem _ hα.2 hβ.2
  reflection_mem α hα β hβ := by
    refine ⟨IsRoot.smul hα.1 _, ?_⟩
    rw [rootReflection_smul hβ.1, sub_eq_add_neg, toRat_add, toRat_neg, toRat_zsmul]
    exact Submodule.add_mem _ hα.2 (Submodule.neg_mem _ (Submodule.smul_mem _ _ hβ.2))
  irreducible S hS hperp :=
    irreducible_of_subset_ratClosure hΨ (subset_ratClosure hΨ.isRoot) le_rfl S hS hperp

end CFSG.LieType.Chevalley
