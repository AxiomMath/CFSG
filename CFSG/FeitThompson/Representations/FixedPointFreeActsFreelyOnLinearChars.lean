module

public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.FeitThompson.Representations.BrauerPermutationLemma
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {P : Type*} [CommGroup P] {u : MulAut P}

theorem fixedPointFree_iff_setOf_fixed_eq_singleton_one {X : Type*} [Group X] (α : MulAut X) :
    MonoidHom.FixedPointFree (α : X → X) ↔ {x : X | α x = x} = {1} := by
  refine ⟨fun h => Set.eq_singleton_iff_unique_mem.2 ⟨map_one α, fun x hx => h x hx⟩,
    fun h x hx => ?_⟩
  have hx' : x ∈ ({1} : Set X) := h ▸ hx
  simpa using hx'

theorem surjective_commutatorMap_of_fixedPointFree {X : Type*} [Group X] [Finite X] {α : MulAut X}
    (hα : MonoidHom.FixedPointFree (α : X → X)) :
    Function.Surjective (MonoidHom.commutatorMap (α : X → X)) :=
  Finite.surjective_of_injective hα.commutatorMap_injective

theorem eq_one_of_forall_apply_aut_eq [Finite P] (hu : MonoidHom.FixedPointFree (u : P → P))
    {lam : P → ℂ} (hlam : lam ∈ Irr P) (h : ∀ p : P, lam (u p) = lam p) : lam = 1 := by
  obtain ⟨ψ, rfl⟩ := exists_linearCharFun_eq_of_mem_Irr hlam
  have hψ : ∀ p : P, ψ (u p) = ψ p := fun p => Units.ext (by simpa using h p)
  funext q
  obtain ⟨p, rfl⟩ := surjective_commutatorMap_of_fixedPointFree hu q
  rw [MonoidHom.commutatorMap_apply]
  simp [map_div, hψ p]

theorem eq_one_of_setOf_fixed_eq_singleton_one [Finite P] (hu : {p : P | u p = p} = {1})
    {lam : P → ℂ} (hlam : lam ∈ Irr P) (h : ∀ p : P, lam (u p) = lam p) (p : P) : lam p = 1 :=
  congrFun (eq_one_of_forall_apply_aut_eq
    ((fixedPointFree_iff_setOf_fixed_eq_singleton_one u).2 hu) hlam h) p

theorem setOf_invariant_mem_Irr_eq_singleton_one [Finite P]
    (hu : MonoidHom.FixedPointFree (u : P → P)) :
    {lam ∈ Irr P | ∀ p : P, lam (u p) = lam p} = {1} := by
  ext lam
  refine ⟨fun ⟨hlam, h⟩ => eq_one_of_forall_apply_aut_eq hu hlam h, ?_⟩
  rintro rfl
  exact ⟨one_mem_Irr, fun _ => rfl⟩

theorem irrAut_eq_self_iff_coe_eq_one [Finite P] (hu : MonoidHom.FixedPointFree (u : P → P))
    (χ : Irr P) : irrAut u χ = χ ↔ (χ : P → ℂ) = 1 := by
  refine ⟨fun h => eq_one_of_forall_apply_aut_eq hu χ.2 ((irrAut_eq_self_iff u χ).1 h), fun h => ?_⟩
  exact (irrAut_eq_self_iff u χ).2 fun p => by rw [h]; rfl

end CFSG.FeitThompson
