module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Hyp
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

theorem rhyp_perm5 : RHyp (Equiv.Perm (Fin 5)) (alternatingGroup (Fin 5)) where
  normal := inferInstance
  simple := alternatingGroup.isSimpleGroup (by simp)
  nonab := by
    refine ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2, ?_,
      Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 3, ?_, ?_⟩
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
    · exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
    · decide
  min := fun N hN hNne => by
    haveI : N.Normal := hN
    exact Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5) (by simp)
      ((Subgroup.nontrivial_iff_ne_bot N).mpr hNne)
  center := fun x h => CFSG.perm_eq_one_of_forall_commute (by simp) fun y => (h y).symm

end CFSG.EvenSporadicStandard.HSStd.InvCent
