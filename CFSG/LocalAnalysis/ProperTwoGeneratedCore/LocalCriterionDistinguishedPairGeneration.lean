module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.ProperTwoGeneratedCore
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def distinguishedCommutator (t : G) (J : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ j ∈ J, x = t⁻¹ * j⁻¹ * t * j}

theorem distinguishedCommutator_eq (t : G) (ht : orderOf t = 2) (J : Subgroup G) :
    distinguishedCommutator t J = ⁅J, Subgroup.zpowers t⁆ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, hj, rfl⟩
    change t⁻¹ * j⁻¹ * t * j ∈ ⁅J, Subgroup.zpowers t⁆
    have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers t) (J.inv_mem hj)
    rw [Subgroup.commutator_comm] at h
    simpa only [commutatorElement_def, inv_eq_self_of_orderOf_eq_two ht, inv_inv] using h
  · apply Subgroup.commutator_le.mpr
    intro j hj a ha
    rcases involution_zpowers_elements ht ha with haone | hat
    · rw [haone, commutatorElement_one_right]
      exact (distinguishedCommutator t J).one_mem
    · rw [hat]
      have h : t⁻¹ * j * t * j⁻¹ ∈ distinguishedCommutator t J :=
        Subgroup.subset_closure ⟨j⁻¹, J.inv_mem hj, by simp only [inv_inv]⟩
      have hi := (distinguishedCommutator t J).inv_mem h
      have heq : ⁅j, t⁆ = (t⁻¹ * j * t * j⁻¹)⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, inv_inv,
          inv_eq_self_of_orderOf_eq_two ht, mul_assoc]
      rw [heq]
      exact hi

theorem center_of_distinguished_commutator_generation (z t u : G)
    (ht : orderOf t = 2) (huz : Commute u z) (hut : Commute u t)
    (J : Subgroup G)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ distinguishedCommutator t J = ⊤)
    (hcomm : ⁅J, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer ({u} : Set G)) :
    u ∈ Subgroup.center G := by
  have hGcentral : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [← hgen]
    refine sup_le (sup_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hut.symm.eq))) ?_
    rwa [distinguishedCommutator_eq t ht J]
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hGcentral (Subgroup.mem_top g))

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
