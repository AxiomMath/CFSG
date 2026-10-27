module

public import Certificates.Data.Kernel.G28.R2
public import Certificates.Data.Kernel.Misc.PermClos
public import CFSG.Certificates.Kernel.G28.R2Sound
import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Quasithin.H13.L32NKGG22
public import Certificates.Data.TitsR2V6
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CFSG.KC.U33

open CFSG.KC.G28R CFSG.Quasithin.H13.KGCert Certificates.TitsR2V6

section Mat

local notation "Mt" => Matrix (Fin 6) (Fin 6) (ZMod 2)

end Mat

end CFSG.KC.U33

end
