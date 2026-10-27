module

public import Mathlib.RingTheory.TensorProduct.Free
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.BaseChange
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.InvariantsTransport

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (bcRep)

theorem finrank_invariants_eq_iInf_toMatrix {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Group G] (ρ : Representation K G V) {n : ℕ} (b : Module.Basis (Fin n) K V) :
    Module.finrank K ↥(Representation.invariants ρ) =
      Module.finrank K ↥(⨅ g : G,
        LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix b b (ρ g)) - 1)) := by
  have hmat : ∀ (g : G) (x : Fin n → K),
      b.equivFun (ρ g (b.equivFun.symm x)) = Matrix.toLin' (LinearMap.toMatrix b b (ρ g)) x := by
    intro g x
    have key := LinearMap.toMatrix_mulVec_repr b b (ρ g) (b.equivFun.symm x)
    have hx : ⇑(b.repr (b.equivFun.symm x)) = x := by
      rw [← Module.Basis.equivFun_apply]
      exact b.equivFun.apply_symm_apply x
    rw [hx] at key
    rw [Matrix.toLin'_apply, key, Module.Basis.equivFun_apply]
  have hmap : (Representation.invariants ρ).map b.equivFun.toLinearMap =
      ⨅ g : G, LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix b b (ρ g)) - 1) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero, Representation.mem_invariants]
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      show Matrix.toLin' (LinearMap.toMatrix b b (ρ g)) (b.equivFun v) = b.equivFun v
      rw [← hmat g, b.equivFun.symm_apply_apply, hv g]
    · intro hx
      refine ⟨b.equivFun.symm x, ?_, b.equivFun.apply_symm_apply x⟩
      intro g
      apply b.equivFun.injective
      rw [hmat g, b.equivFun.apply_symm_apply]
      exact hx g
  rw [← hmap]
  exact LinearEquiv.finrank_eq
    ((Representation.invariants ρ).equivMapOfInjective b.equivFun.toLinearMap
      b.equivFun.injective)

theorem finrank_invariants_bcRep_le {K k G W : Type*} [Field K] [Field k] [Algebra K k]
    [AddCommGroup W] [Module K W] [Module.Finite K W] [Group G] [Finite G]
    (ρ : Representation K G W) :
    Module.finrank k ↥(Representation.invariants (bcRep k ρ)) ≤
      Module.finrank K ↥(Representation.invariants ρ) := by
  let b := Module.finBasis K W
  have hN : ∀ g : G,
      LinearMap.toMatrix (Algebra.TensorProduct.basis k b) (Algebra.TensorProduct.basis k b)
          (bcRep k ρ g) =
        (LinearMap.toMatrix b b (ρ g)).map (algebraMap K k) :=
    fun g => LinearMap.toMatrix_baseChange k (ρ g) b b
  have h1 := finrank_invariants_le_of_basis (algebraMap K k) (bcRep k ρ)
    (Algebra.TensorProduct.basis k b) (fun g => LinearMap.toMatrix b b (ρ g)) hN
  exact h1.trans (finrank_invariants_eq_iInf_toMatrix ρ b).symm.le

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
