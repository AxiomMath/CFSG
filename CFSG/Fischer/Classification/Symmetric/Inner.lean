module


import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.Fischer.Classification.SymPair

open Equiv Equiv.Perm

theorem exists_eq_conj_of_mulEquiv_perm {G : Type*} [Group G] {D : Set G} {m : ℕ} (hm : 3 ≤ m)
    (φ : G ≃* Perm (Fin m)) (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) (ψ : MulAut G)
    (hψ : ∀ g, g ∈ D ↔ ψ g ∈ D) : ∃ x : G, ψ = MulAut.conj x := by
  let f : Perm (Fin m) →* Perm (Fin m) :=
    (φ.toMonoidHom.comp ψ.toMonoidHom).comp φ.symm.toMonoidHom
  have hf : ∀ σ, f σ = φ (ψ (φ.symm σ)) := fun _ => rfl
  have hinj : Function.Injective f := fun σ τ hστ => by
    rw [hf, hf] at hστ
    exact φ.symm.injective (ψ.injective (φ.injective hστ))
  have hswap : ∀ σ : Perm (Fin m), σ.IsSwap → (f σ).IsSwap := fun σ hσ => by
    rw [hf]
    refine (hφ _).1 ((hψ _).1 ((hφ _).2 ?_))
    rwa [MulEquiv.apply_symm_apply]
  obtain ⟨π, hπ⟩ := CFSG.StandardType.exists_eq_conj_of_isSwap hm f hinj hswap
  refine ⟨φ.symm π, MulEquiv.ext fun y => φ.injective ?_⟩
  have := hπ (φ y)
  rw [hf, MulEquiv.symm_apply_apply] at this
  rw [this, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.Fischer.Classification.SymPair
