module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Ree.FixedSubgroupData
public import CFSG.LieType.Ree.ReeHolds

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open scoped commutatorElement

theorem isPerfect_of_isSimpleGroup_of_exists_ne {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  rcases (inferInstance : (commutator S).Normal).eq_bot_or_eq_top with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hmem : ⁅a, b⁆ ∈ commutator S := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · exact ⟨h1⟩

section Ree

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem finiteReeFixedGroup_eq_reeFixed_F4 (a : ℕ) :
    ReeTag.F4.finiteReeFixedGroup K a = reeFixed ReeTag.F4 K a := by
  apply map_injective (adjointGroup ReeTag.F4.tag K).subtype_injective
  change ReeTag.F4.reeGamma K a = _
  rw [ReeTag.reeGamma_eq_reeFixedGroup, reeFixedGroup_eq_map_reeFixed]

end Ree

end CFSG.SeitzReduction.F4Pilot
