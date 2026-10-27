module

public import CFSG.ClassicalInvolution.Q3.Q3TJD4
public import CFSG.ClassicalInvolution.Q3.Q3TIMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

theorem quasisimpleConnected3_of_outer (h : AlmostSimpleOuter3) : QuasisimpleConnected3 :=
  quasisimpleConnected3_of_residuals modelOddAutRigid_proved h

end CFSG.ClassicalInvolution.Q3.Q3T
