module

public import Certificates.Data.Kernel.ThCent.Pin
public import CFSG.Certificates.Kernel.ThCent.PinSound
public import CFSG.Certificates.Kernel.ThCent.ListSound
public import CFSG.Sporadic.ThSchreier.LocalData

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.Sporadic.ThSchreier
  Pointwise

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

end CFSG.KC.ThCent

end
