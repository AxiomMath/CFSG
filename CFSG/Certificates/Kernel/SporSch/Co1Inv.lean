module

public import Certificates.Data.CFSGNative.Co1Schreier.Base
import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2

theorem inv_eq_of_mul {X Y : Rows} (h : (wf X && wf Y && mul X Y == one ()) = true) :
    inv X = Y := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, hwY⟩, hm⟩ := h
  unfold wf at hwY
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hwY
  obtain ⟨hY, hYr⟩ := hwY
  refine M24.MatL.inv_eq_of_mul ?_ hY fun i hi => ?_
  · rw [← rowsMatrix_mulRows]
    change rowsMatrix 24 (mul X Y) = 1
    rw [hm]
    exact rowsMatrix_idRows 24
  · have hi' : i < Y.size := by omega
    rw [Array.getElem?_eq_getElem hi', Option.getD_some]
    exact hYr i hi'

end CFSG.KS.SporSch

end
