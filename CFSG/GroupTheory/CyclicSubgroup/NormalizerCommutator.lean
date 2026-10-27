module


public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.GroupTheory.CyclicSubgroup

open scoped commutatorElement

theorem commutator_le_centralizer {H : Type*} [Group H] [Finite H] (R : Subgroup H)
    [IsCyclic R] (U B : Subgroup H) (hU : U ≤ Subgroup.normalizer (R : Set H))
    (hB : B ≤ Subgroup.normalizer (R : Set H)) :
    ⁅U, B⁆ ≤ Subgroup.centralizer (R : Set H) := by
  have hcomm : ∀ φ ψ : MulAut R, φ * ψ = ψ * φ := fun φ ψ => by
    apply (IsCyclic.mulAutMulEquiv R).injective
    rw [map_mul, map_mul, mul_comm]
  rw [Subgroup.commutator_le]
  intro u hu b hb
  have hc : ⁅u, b⁆ ∈ Subgroup.normalizer (R : Set H) :=
    (Subgroup.normalizer (R : Set H)).mul_mem
      ((Subgroup.normalizer (R : Set H)).mul_mem
        ((Subgroup.normalizer (R : Set H)).mul_mem (hU hu) (hB hb))
        ((Subgroup.normalizer (R : Set H)).inv_mem (hU hu)))
      ((Subgroup.normalizer (R : Set H)).inv_mem (hB hb))
  have hker : (⟨⁅u, b⁆, hc⟩ : Subgroup.normalizer (R : Set H)) ∈
      R.normalizerMonoidHom.ker := by
    have : (⟨⁅u, b⁆, hc⟩ : Subgroup.normalizer (R : Set H)) =
        ⁅(⟨u, hU hu⟩ : Subgroup.normalizer (R : Set H)), ⟨b, hB hb⟩⁆ := rfl
    rw [this, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact hcomm _ _
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact hker

end CFSG.GroupTheory.CyclicSubgroup
