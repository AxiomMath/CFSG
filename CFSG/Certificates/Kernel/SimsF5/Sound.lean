module

public import Certificates.Data.Kernel.SimsF5.Defs
public import CFSG.Certificates.Kernel.CosetLat.MatEnc

public section

namespace CFSG.KC.SimsF5

open CFSG.KC.Ord CFSG.KC.CosetLat
open CFSG.KC.Misc.Clos (ClosEnc)

theorem consts6 : constsOK 3 6 36 6 3 l6L l6H l6CM l6RM l6ONE l6LV l6HV = true := by
  decide +kernel

theorem m6_enc :
    ClosEnc (fun g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3) => matCode 3 6 6 g) m6 l6ONE :=
  matCode_enc consts6

end CFSG.KC.SimsF5

end
