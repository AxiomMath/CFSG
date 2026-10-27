module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.BaseChange
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.RingTheory.TensorProduct.Free

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors TensorProduct

section BC

variable {K : Type*} [Field K] {k : Type*} [Field k] [Algebra K k] {V : Type*} [AddCommGroup V]
  [Module K V] [Module.Finite K V]

theorem linearIndependent_bcVec {ι : Type*} {w : ι → V} (hw : LinearIndependent K w) :
    LinearIndependent k (fun i => bcVec (K := K) k (w i)) := by
  classical
  let b := Module.finBasis K V
  let B := Algebra.TensorProduct.basis k b
  have h1 : LinearIndependent K (fun i => b.equivFun (w i)) :=
    hw.map' b.equivFun.toLinearMap (LinearMap.ker_eq_bot.2 b.equivFun.injective)
  have h2 : LinearIndependent k (fun i => algebraMap K k ∘ b.equivFun (w i)) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  have h3 := h2.map' B.equivFun.symm.toLinearMap
    (LinearMap.ker_eq_bot.2 B.equivFun.symm.injective)
  convert h3 using 2 with i
  symm
  rw [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  funext j
  simp only [Module.Basis.equivFun_apply, bcVec, B, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply, Function.comp_apply]

theorem finrank_range_le_bc (f : V →ₗ[K] V) :
    Module.finrank K (LinearMap.range f) ≤
      Module.finrank k (LinearMap.range (f.baseChange k)) := by
  classical
  let c := Module.finBasis K (LinearMap.range f)
  have hli : LinearIndependent K (fun j => ((c j : LinearMap.range f) : V)) :=
    c.linearIndependent.map' (LinearMap.range f).subtype (by simp)
  have h2 := linearIndependent_bcVec (k := k) hli
  have hmem : ∀ j, bcVec (K := K) k ((c j : LinearMap.range f) : V) ∈
      LinearMap.range (f.baseChange k) := by
    intro j
    obtain ⟨x, hx⟩ := (c j).2
    refine ⟨bcVec k x, ?_⟩
    show (f.baseChange k) ((1 : k) ⊗ₜ[K] x) = (1 : k) ⊗ₜ[K] ((c j : LinearMap.range f) : V)
    rw [LinearMap.baseChange_tmul, hx]
  have h3 : LinearIndependent k (fun j => (⟨_, hmem j⟩ : LinearMap.range (f.baseChange k))) :=
    LinearIndependent.of_comp (LinearMap.range (f.baseChange k)).subtype h2
  have : Module.Finite k (k ⊗[K] V) := Module.Finite.of_basis (Algebra.TensorProduct.basis k (Module.finBasis K V))
  simpa using h3.fintype_card_le_finrank

end BC

section Twist

variable {k : Type*} [Field k] {G V : Type*} [Group G] [AddCommGroup V] [Module k V]

theorem finrank_range_twist (θ : k ≃+* k) (ρ : Representation k G V) (g : G) :
    Module.finrank k (LinearMap.range (twistRep θ ρ g - 1)) =
      Module.finrank k (LinearMap.range (ρ g - 1)) := by
  unfold Module.finrank
  congr 1
  refine rank_eq_of_equiv_equiv θ
    { toFun := fun x => ⟨(show V from x.1), by
        obtain ⟨v, hv⟩ := x.2
        exact ⟨(show V from v), hv⟩⟩
      invFun := fun x => ⟨(show FrobTwist θ V from x.1), by
        obtain ⟨v, hv⟩ := x.2
        exact ⟨(show FrobTwist θ V from v), hv⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl } θ.bijective (fun r x => rfl)

end Twist

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
