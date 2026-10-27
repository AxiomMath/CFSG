module

public import CFSG.Certificates.Kernel.E27Orth.Sound
public import CFSG.Certificates.Kernel.J4Hub.RegSound

public section

namespace CFSG.KD.E27Orth

open CFSG.KC.Ord CFSG.KS.Ord

theorem encLane {p w S d T L H CM RM ONE LV HV nb : ℕ}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S) :
    Enc (ordMat p d w S) (mulR p w S d T L H CM RM) (validM p nb L H) where
  hmul _ _ ha hb := (CFSG.KS.J4Hub.mul_sound' hc hnb ha hb).2
  hinj _ _ ha hb h := CFSG.KS.J4Hub.ordMat_inj' hc hnb ha hb h

theorem oneLane {p w S d T L H CM RM ONE LV HV nb : ℕ}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S) :
    validM p nb L H ONE = true ∧ ordMat p d w S ONE = 1 :=
  CFSG.KS.J4Hub.one_sound' hc hnb

end CFSG.KD.E27Orth

end
