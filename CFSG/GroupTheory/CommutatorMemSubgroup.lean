module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def commMemSubgroup (L N : Subgroup G) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (v : G) : Subgroup G where
  carrier := {g | g ∈ L ∧ ⁅g, v⁆ ∈ N}
  one_mem' := ⟨L.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haL, haN⟩ ⟨hbL, hbN⟩
    refine ⟨L.mul_mem haL hbL, ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLN haL) _).mp hbN) haN
  inv_mem' := by
    rintro a ⟨haL, haN⟩
    refine ⟨L.inv_mem haL, ?_⟩
    rw [commutatorElement_inv_left]
    simpa [commutatorElement_inv] using
      (Subgroup.mem_normalizer_iff.mp (hLN (L.inv_mem haL)) (⁅a, v⁆⁻¹)).mp (N.inv_mem haN)

@[simp] theorem mem_commMemSubgroup {L N : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (v g : G) :
    g ∈ commMemSubgroup L N hLN v ↔ g ∈ L ∧ ⁅g, v⁆ ∈ N :=
  Iff.rfl

theorem commMemSubgroup_le (L N : Subgroup G) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (v : G) : commMemSubgroup L N hLN v ≤ L := fun _ hg => hg.1

end CFSG.GroupTheory
