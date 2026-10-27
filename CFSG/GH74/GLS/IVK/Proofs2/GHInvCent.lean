module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup

theorem map_centralizer_singleton' {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    (centralizer ({a} : Set A)).map φ.toMonoidHom = centralizer ({φ a} : Set B) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hx]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy

@[expose] noncomputable def centralizerEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A)
    (b : B) (h : φ a = b) : ↥(centralizer ({a} : Set A)) ≃* ↥(centralizer ({b} : Set B)) :=
  (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr ((map_centralizer_singleton' φ a).trans (by rw [h])))

theorem coe_centralizerEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) (b : B)
    (h : φ a = b) (x : ↥(centralizer ({a} : Set A))) :
    ((centralizerEquiv φ a b h x : ↥(centralizer ({b} : Set B))) : B) = φ (x : A) := rfl

theorem card_centralizer_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    Nat.card ↥(centralizer ({a} : Set A)) = Nat.card ↥(centralizer ({φ a} : Set B)) :=
  Nat.card_congr (centralizerEquiv φ a (φ a) rfl).toEquiv

theorem card_centralizer_subtype {M : Type*} [Group M] (Γ : Subgroup M) (x : ↥Γ) :
    Nat.card ↥(centralizer ({x} : Set ↥Γ)) = Nat.card ↥(Γ ⊓ centralizer ({(x : M)} : Set M)) := by
  have hmap : (centralizer ({x} : Set ↥Γ)).map Γ.subtype = Γ ⊓ centralizer ({(x : M)} : Set M) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hy, hc⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hc, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective Γ.subtype_injective]

end CFSG.GH74.GLS.IVK.GHInv
