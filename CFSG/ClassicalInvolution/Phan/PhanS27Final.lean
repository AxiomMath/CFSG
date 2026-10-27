module

public import CFSG.ClassicalInvolution.Phan.PhanS21Q7Sound
public import CFSG.ClassicalInvolution.Phan.PhanS22WittB
public import CFSG.ClassicalInvolution.Phan.PhanS23SigmaF
public import CFSG.ClassicalInvolution.Phan.PhanS24Trans
public import CFSG.ClassicalInvolution.Phan.PhanS26Class

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

theorem sigmaWitt : SigmaWitt :=
  sigmaWitt_of_witt exists_isometryEquiv_of_family

@[expose] def repsOfData : List ClassRep :=
  (List.range q7RepsData.size).map fun i =>
    { γ := gfDec (q7RepsData[i]!)[0]!, η := gfDec (q7RepsData[i]!)[1]!,
      br := (q7RepsData[i]!)[2]!, c := repVec i }

theorem tableOK_data : TableOK repsOfData :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

theorem repConn_of_check (h : q7MuCheck = true) : ∀ r ∈ repsOfData, RepConn r.c := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
  intro A C hA hC
  exact q7MuCheck_sound h (List.mem_range.1 hi) hA hC

theorem muConnected_m0_of_check (h : q7MuCheck = true) : Std.Q.MuConnected m0 :=
  muConnected_m0 sigmaWitt tableOK_data (repConn_of_check h)

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

namespace CFSG.ClassicalInvolution.PhanB3.S

theorem q7Residual_of_check (h : Std.Q7.q7MuCheck = true) : Q7Residual :=
  Std.Q7.q7Residual_of_muConnected_m0 (Std.Q7.muConnected_m0_of_check h)

end CFSG.ClassicalInvolution.PhanB3.S
