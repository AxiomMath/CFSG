module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] {U A : Subgroup G}

theorem isMulCommutative_inf_centralizer_sup (hAU : A ≤ U) [IsMulCommutative A] :
    IsMulCommutative ↥((U ⊓ Subgroup.centralizer (U : Set G)) ⊔ A) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure ?_
  rintro x (hxU | hxA) y (hyU | hyA) -
  · exact ((Subgroup.mem_centralizer_iff.1 hxU.2) y hyU.1).symm
  · exact ((Subgroup.mem_centralizer_iff.1 hxU.2) y (hAU hyA)).symm
  · exact (Subgroup.mem_centralizer_iff.1 hyU.2) x (hAU hxA)
  · exact congrArg Subtype.val (mul_comm' (⟨x, hxA⟩ : A) ⟨y, hyA⟩)

theorem le_normalizer_inf_centralizer_sup (hAU : A ≤ U)
    (hU : ⁅U, U⁆ ≤ Subgroup.centralizer (U : Set G)) :
    U ≤ Subgroup.normalizer
      (((U ⊓ Subgroup.centralizer (U : Set G)) ⊔ A : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  have hUA : (U ⊓ Subgroup.centralizer (U : Set G)) ⊔ A ≤ U := sup_le inf_le_left hAU
  refine (le_inf (Subgroup.commutator_le_of_le le_rfl hUA) ?_).trans le_sup_left
  exact (Subgroup.commutator_mono le_rfl hUA).trans hU

end CFSG.GroupTheory

end
