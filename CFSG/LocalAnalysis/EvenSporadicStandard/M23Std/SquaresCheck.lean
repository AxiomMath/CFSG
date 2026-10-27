module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.M23SylowGroup

public section

namespace CFSG.EvenSporadicStandard.M23Std.SquaresCheck

open CFSG.EvenSporadicStandard.Wong77.M23Sylow

theorem squares_table :
    tmul (tmul (wordTab gensTab [4, 6]) (wordTab gensTab [4, 6]))
        (tmul (wordTab gensTab [0, 6]) (wordTab gensTab [0, 6])) ≠
      tmul (tmul (wordTab gensTab [0, 6]) (wordTab gensTab [0, 6]))
        (tmul (wordTab gensTab [4, 6]) (wordTab gensTab [4, 6])) := by
  decide

theorem wordElt_sylowGens_mem (w : List Nat) : wordElt sylowGens w ∈ sylowS := by
  induction w with
  | nil => exact sylowS.one_mem
  | cons i w ih =>
    refine sylowS.mul_mem ?_ ih
    by_cases hi : i < sylowGens.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact sylowGens_mem (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi)]
      exact sylowS.one_mem

theorem exists_noncomm_squares :
    ∃ x ∈ sylowS, ∃ w ∈ sylowS, x * x * (w * w) ≠ w * w * (x * x) := by
  refine ⟨wordElt sylowGens [4, 6], wordElt_sylowGens_mem _, wordElt sylowGens [0, 6],
    wordElt_sylowGens_mem _, fun h => squares_table ?_⟩
  simpa only [tab_mul, tab_wordElt, tab_sylowGens] using congrArg tab h

end CFSG.EvenSporadicStandard.M23Std.SquaresCheck
