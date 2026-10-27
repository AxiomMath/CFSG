module

public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.GH74.GLS.Stage4.Rest.Mix11cK

open scoped MonoidAlgebra
open Representation

variable {k : Type*} [Field k] {G K : Type*} [Group G] [Group K]
  {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

@[expose] def infl (π : G →* K) (σ : Representation k K W) : Representation k G W := σ.comp π

@[simp] theorem infl_apply (π : G →* K) (σ : Representation k K W) (g : G) : infl π σ g = σ (π g) := rfl

theorem isIntertwiningMap_comp_iff (π : G →* K) (hπ : Function.Surjective π)
    (σ : Representation k K W) (σ' : Representation k K W') (f : W →ₗ[k] W') :
    IsIntertwiningMap (infl π σ) (infl π σ') f ↔ IsIntertwiningMap σ σ' f := by
  constructor
  · intro h
    refine ⟨fun x v => ?_⟩
    obtain ⟨g, rfl⟩ := hπ x
    exact h.isIntertwining g v
  · intro h
    exact ⟨fun g v => h.isIntertwining (π g) v⟩

def subrepCompOrderIso (π : G →* K) (hπ : Function.Surjective π) (σ : Representation k K W) :
    Subrepresentation σ ≃o Subrepresentation (infl π σ) where
  toFun S := ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (π g) hv⟩
  invFun T := ⟨T.toSubmodule, fun x v hv => by
    obtain ⟨g, rfl⟩ := hπ x
    exact T.apply_mem_toSubmodule g hv⟩
  left_inv S := rfl
  right_inv T := rfl
  map_rel_iff' := Iff.rfl

theorem isSimpleModule_comp_iff (π : G →* K) (hπ : Function.Surjective π)
    (σ : Representation k K W) :
    IsSimpleModule k[G] (infl π σ).asModule ↔ IsSimpleModule k[K] σ.asModule := by
  rw [← irreducible_iff_isSimpleModule_asModule, ← irreducible_iff_isSimpleModule_asModule]
  exact (OrderIso.isSimpleOrder_iff (subrepCompOrderIso π hπ σ)).symm

theorem exists_ne_one_comp_iff (π : G →* K) (hπ : Function.Surjective π)
    (σ : Representation k K W) :
    (∃ g, (infl π σ) g ≠ 1) ↔ ∃ x, σ x ≠ 1 := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨π g, hg⟩
  · rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := hπ x
    exact ⟨g, hx⟩

theorem nonempty_equiv_of_comp (π : G →* K) (hπ : Function.Surjective π)
    (σ1 : Representation k K W) (σ2 : Representation k K W')
    (e : (infl π σ1).asModule ≃ₗ[k[G]] (infl π σ2).asModule) :
    Nonempty (σ1.asModule ≃ₗ[k[K]] σ2.asModule) := by
  let f : IntertwiningMap (infl π σ1) (infl π σ2) :=
    (IntertwiningMap.equivLinearMapAsModule (infl π σ1) (infl π σ2)).symm
      (e : (infl π σ1).asModule →ₗ[k[G]] (infl π σ2).asModule)
  have hf : IsIntertwiningMap σ1 σ2 f.toLinearMap :=
    (isIntertwiningMap_comp_iff π hπ σ1 σ2 f.toLinearMap).1 ⟨f.isIntertwining⟩
  let f' : IntertwiningMap σ1 σ2 :=
    f.toLinearMap.intertwiningMap_of_isIntertwiningMap σ1 σ2 hf.isIntertwining
  have hbij : Function.Bijective (IntertwiningMap.equivLinearMapAsModule σ1 σ2 f') := e.bijective
  exact ⟨LinearEquiv.ofBijective _ hbij⟩

theorem card_end_comp (π : G →* K) (hπ : Function.Surjective π) (σ : Representation k K W) :
    Nat.card (Module.End k[G] (infl π σ).asModule) = Nat.card (Module.End k[K] σ.asModule) := by
  refine Nat.card_congr ?_
  refine (IntertwiningMap.equivAlgEnd (ρ := σ.comp π)).symm.toEquiv.trans ?_
  refine Equiv.trans ?_ (IntertwiningMap.equivAlgEnd (ρ := σ)).toEquiv
  exact
    { toFun := fun f => f.toLinearMap.intertwiningMap_of_isIntertwiningMap σ σ
        ((isIntertwiningMap_comp_iff π hπ σ σ f.toLinearMap).1 ⟨f.isIntertwining⟩).isIntertwining
      invFun := fun f => f.toLinearMap.intertwiningMap_of_isIntertwiningMap (infl π σ) (infl π σ)
        ((isIntertwiningMap_comp_iff π hπ σ σ f.toLinearMap).2 ⟨f.isIntertwining⟩).isIntertwining
      left_inv := fun f => IntertwiningMap.ext rfl
      right_inv := fun f => IntertwiningMap.ext rfl }

end CFSG.GH74.GLS.Stage4.Rest.Mix11cK
