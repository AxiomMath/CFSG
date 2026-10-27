module

public import Certificates.Data.Kernel.GMS78RuSCent
import CFSG.Certificates.Kernel.GMS78RuSC.Main

public section

namespace CFSG.KC.GMS

theorem kAll17_sound (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO u k : Nat)
    (h : kAll17 GT DPR LIN DM DO u k = true) :
    kKey17 (mul17K GT DPR LIN DM DO) u k = true ∧ kClo17 (mul17K GT DPR LIN DM DO) u k = true := by
  exact SC.kAll17_sound GT DPR LIN DM DO u k h

end CFSG.KC.GMS

end
