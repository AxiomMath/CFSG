module

public import Mathlib.RepresentationTheory.Invariants
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.FixBaseChange

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

theorem finrank_invariants_of_linearEquiv {k G V W : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) (e : V ≃ₗ[k] W)
    (he : ∀ (g : G) (v : V), e (ρ g v) = σ g (e v)) :
    Module.finrank k ↥(Representation.invariants ρ) =
      Module.finrank k ↥(Representation.invariants σ) := by
  have hmap : (Representation.invariants ρ).map e.toLinearMap = Representation.invariants σ := by
    ext w
    simp only [Submodule.mem_map, Representation.mem_invariants]
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      show σ g (e v) = e v
      rw [← he g v, hv g]
    · intro hw
      refine ⟨e.symm w, ?_, by simp⟩
      intro g
      apply e.injective
      rw [he g, e.apply_symm_apply]
      exact hw g
  rw [← hmap]
  exact LinearEquiv.finrank_eq
    ((Representation.invariants ρ).equivMapOfInjective e.toLinearMap e.injective)

theorem finrank_invariants_le_of_basis {K k V : Type*} [Field K] [Field k]
    [AddCommGroup V] [Module k V] (ι : K →+* k)
    {G : Type*} [Group G] [Finite G] (ρ : Representation k G V) {n : ℕ} (b : Module.Basis (Fin n) k V)
    (N : G → Matrix (Fin n) (Fin n) K)
    (hN : ∀ g, LinearMap.toMatrix b b (ρ g) = (N g).map ι) :
    Module.finrank k ↥(Representation.invariants ρ) ≤
      Module.finrank K ↥(⨅ g : G, LinearMap.ker (Matrix.toLin' (N g) - 1)) := by
  have hmat : ∀ (g : G) (x : Fin n → k),
      b.equivFun (ρ g (b.equivFun.symm x)) = Matrix.toLin' ((N g).map ι) x := by
    intro g x
    have key := LinearMap.toMatrix_mulVec_repr b b (ρ g) (b.equivFun.symm x)
    have hx : ⇑(b.repr (b.equivFun.symm x)) = x := by
      rw [← Module.Basis.equivFun_apply]
      exact b.equivFun.apply_symm_apply x
    rw [hx] at key
    rw [← hN g, Matrix.toLin'_apply, key, Module.Basis.equivFun_apply]
  have hmap : (Representation.invariants ρ).map b.equivFun.toLinearMap =
      ⨅ g : G, LinearMap.ker (Matrix.toLin' ((N g).map ι) - 1) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero, Representation.mem_invariants]
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      show Matrix.toLin' ((N g).map ι) (b.equivFun v) = b.equivFun v
      rw [← hmat g, b.equivFun.symm_apply_apply, hv g]
    · intro hx
      refine ⟨b.equivFun.symm x, ?_, b.equivFun.apply_symm_apply x⟩
      intro g
      apply b.equivFun.injective
      rw [hmat g, b.equivFun.apply_symm_apply]
      exact hx g
  have hfin : Module.finrank k ↥(Representation.invariants ρ) =
      Module.finrank k ↥(⨅ g : G, LinearMap.ker (Matrix.toLin' ((N g).map ι) - 1)) := by
    rw [← hmap]
    exact LinearEquiv.finrank_eq
      ((Representation.invariants ρ).equivMapOfInjective b.equivFun.toLinearMap
        b.equivFun.injective)
  rw [hfin]
  exact finrank_fix_map_le ι N

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
