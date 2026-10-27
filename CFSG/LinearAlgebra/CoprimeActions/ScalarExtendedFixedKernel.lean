module


public import CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedFixedKernel

open TensorProduct CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary

variable {F K G V : Type*} [Field F] [Field K] [Algebra F K] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem kernel_eq_bot (ρ : Representation F G V) (d : G)
    (h : LinearMap.ker (ρ d - LinearMap.id) = ⊥) :
    LinearMap.ker (extend (K := K) ρ d - LinearMap.id) = ⊥ := by
  have extend_sub_id (ρ : Representation F G V) (d : G) :
      extend (K := K) ρ d - LinearMap.id = (ρ d - LinearMap.id).baseChange K := by
    rw [extend_apply]
    simp
  rw [extend_sub_id, LinearMap.ker_eq_bot] at *
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ h

theorem cyclic_invariants_eq_ker (ρ : Representation F G V) (D : Subgroup G) (d : G)
    (hd : D = Subgroup.zpowers d) :
    (⨅ e ∈ D, LinearMap.ker (ρ e - LinearMap.id)) = LinearMap.ker (ρ d - LinearMap.id) := by
  apply le_antisymm
  · exact iInf₂_le d (hd ▸ Subgroup.mem_zpowers d)
  · intro x hx
    simp only [Submodule.mem_iInf]
    intro e he
    let S : Subgroup G :=
      { carrier := {g | ρ g x = x}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at *
          rw [map_mul]; simp [hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at *
          calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha]
            _ = x := by rw [← Module.End.mul_apply, ← map_mul]; simp }
    have : D ≤ S := by
      rw [hd, Subgroup.zpowers_le]
      have := LinearMap.mem_ker.mp hx
      show ρ d x = x
      simpa [sub_eq_zero] using this
    have := this he
    simpa [S, sub_eq_zero] using this

theorem cyclic_invariants_eq_bot (ρ : Representation F G V) (D : Subgroup G) (d : G)
    (hd : D = Subgroup.zpowers d)
    (h : (⨅ e ∈ D, LinearMap.ker (ρ e - LinearMap.id)) = ⊥) :
    (⨅ e ∈ D, LinearMap.ker (extend (K := K) ρ e - LinearMap.id)) = ⊥ := by
  rw [cyclic_invariants_eq_ker _ D d hd] at h ⊢
  exact kernel_eq_bot ρ d h

end CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedFixedKernel
