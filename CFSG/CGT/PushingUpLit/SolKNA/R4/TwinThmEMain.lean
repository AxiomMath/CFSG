module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEApply
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEO2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESecFin
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmE189
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEEnd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESev3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmE186

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace ThmE

section Main

theorem thmEAll_of_endC {r : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (hend : E18_endC r) : ThmEAll r :=
  have h6 : E18_6 r := e18_6_of (by omega) e18_5 (e18_6O2_of e18_5 (e18_6NotO2_of_four_le hr))
  have h7 : E18_7 r := e18_7_of hr h6 e18_4C
  thmEAll_of_minCexFalse
    (minCexFalse_of_steps configSylowCentralizer h6 (e18_8z_of_e18_7 h7) (e18_9_of hr hNo h7) hend)

end Main

section MainEnd

theorem thmEAll_of_noQ16E4 {r : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) : ThmEAll r :=
  thmEAll_of_endC hr hNo (e18_endC_of (by omega))

theorem twinThmER_of_inputs {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (hX : ExtendR r n)
    (h4 : Thm4TwinSupplyR r n) : TwinThmER r n :=
  twinThmER_of_thmEAll (thmEAll_of_noQ16E4 hr hNo) hX h4

end MainEnd

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
