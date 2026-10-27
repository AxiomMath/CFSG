module

public import CFSG.Certificates.Kernel.FixBoundK.BasicsSound
public import CFSG.Certificates.Kernel.FixBoundK.RepGlue

public section

namespace CFSG.KC.FixBoundK

theorem basicsSem : BasicsSem := fun _ _ h => basicsOK_bit h

end CFSG.KC.FixBoundK

end
