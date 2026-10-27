module


public import CFSG.Certificates.Kernel.SporSch.ThirdChainHBase

public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

variable (h : ThirdFactsH)
include h

theorem locU_fixH
    {j : ℕ} (hj : j < 12) : locU (bpt j) = bpt j := by
  apply Fin.ext
  rw [rep_apply_bptH h rep_u (j := j) (by omega), bpt_valH h (j := j) (by omega)]
  have := allLt_iff.1 h.u_fix j hj
  simpa using this

end CFSG.Sporadic.Co2Schreier
