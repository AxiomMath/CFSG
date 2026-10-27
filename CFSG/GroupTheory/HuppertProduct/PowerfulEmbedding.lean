module

public import CFSG.GroupTheory.HuppertProduct.Mho
public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.GroupTheory.HuppertProduct.CubeCommutator
import CFSG.GroupTheory.HuppertProduct.CommutatorClosure
import CFSG.GroupTheory.HuppertProduct.NilpotentAbsorption

public section

open scoped commutatorElement

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem commutator_mho_le_mho_mho [Finite G] {H : Subgroup G} (hH : IsPGroup 3 H)
    (hcomm : ⁅H, H⁆ ≤ mho H 3) : ⁅mho H 3, H⁆ ≤ mho (mho H 3) 3 := by
  haveI : Group.IsNilpotent H := hH.isNilpotent
  have hMH : mho H 3 ≤ H := mho_le H 3
  have hQH : mho (mho H 3) 3 ≤ H := (mho_le _ 3).trans hMH
  have hQn : H ≤ Subgroup.normalizer ((mho (mho H 3) 3 : Subgroup G) : Set G) :=
    le_normalizer_mho_mho H 3 3
  have hLn : H ≤ Subgroup.normalizer ((⁅⁅mho H 3, H⁆, H⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right ⁅mho H 3, H⁆ H
  have hKn : H ≤ Subgroup.normalizer
      ((mho (mho H 3) 3 ⊔ ⁅⁅mho H 3, H⁆, H⁆ : Subgroup G) : Set G) :=
    le_normalizer_sup hQn hLn
  have step1 : ∀ x ∈ H, ∀ g ∈ H, ⁅x ^ 3, g⁆ ∈ mho (mho H 3) 3 ⊔ ⁅⁅mho H 3, H⁆, H⁆ := by
    intro x hx g hg
    have hdM : ⁅g, x⁆ ∈ mho H 3 := hcomm (Subgroup.commutator_mem_commutator hg hx)
    refine cube_commutator_mem hKn hx hg ?_ ?_
    · exact Subgroup.mem_sup_left (pow_mem_mho hdM)
    · intro h hh
      have hL : ⁅x, ⁅g, x⁆⁆ ∈ ⁅mho H 3, H⁆ := by
        rw [← commutatorElement_inv]
        exact (⁅mho H 3, H⁆).inv_mem (Subgroup.commutator_mem_commutator hdM hx)
      exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hL hh)
  have step2 : ⁅mho H 3, H⁆ ≤ mho (mho H 3) 3 ⊔ ⁅⁅mho H 3, H⁆, H⁆ :=
    commutator_mho_le hKn step1
  exact le_of_le_sup_commutator inferInstance hQH hQn
    (Subgroup.commutator_le_of_le hMH le_rfl) step2

end CFSG.GroupTheory.HuppertProduct
