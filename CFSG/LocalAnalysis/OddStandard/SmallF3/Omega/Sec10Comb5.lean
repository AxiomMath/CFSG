module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem exists_alt_permVec_weight_four (v u : Fin 5 → ZMod 2) (hv : vecWeight v = 4)
    (hu : vecWeight u = 4) : ∃ σ ∈ alternatingGroup (Fin 5), permVec σ v = u := by
  revert v u
  unfold vecWeight permVec
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem even_weight_cases_five (w : Fin 5 → ZMod 2) (hw : IsEvenVec w) :
    w = 0 ∨ vecWeight w = 2 ∨ vecWeight w = 4 := by
  revert w
  unfold IsEvenVec vecWeight
  decide +kernel

theorem weight_two_sum_five (w : Fin 5 → ZMod 2) (hw : vecWeight w = 2) :
    ∃ x y : Fin 5 → ZMod 2, vecWeight x = 4 ∧ vecWeight y = 4 ∧ w = x + y := by
  revert w
  unfold vecWeight
  decide +kernel

theorem isEvenVec_of_weight_four (w : Fin 5 → ZMod 2) (hw : vecWeight w = 4) : IsEvenVec w := by
  revert w
  unfold IsEvenVec vecWeight
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
