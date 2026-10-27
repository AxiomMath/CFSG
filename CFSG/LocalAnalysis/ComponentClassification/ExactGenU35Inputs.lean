module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenParse
public import Certificates.Data.ExactGen.U35Text
public import Certificates.Data.HNUnitaryBridge

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

open HNUnitaryBridge

@[expose] def u35FC (_ : Unit := ()) : FCCert := parseFC 50 ExactGenData.u35Text

@[expose] def u35FCCheck (_ : Unit := ()) : Bool :=
  let c := u35FC ()
  c.ok 50 && decide (c.ctx.chP.k = 6) && (c.ctx.chP.S.extract 0 6 == smallPerms) &&
    decide (c.ctx.chP.order 50 = 126000) && decide (c.ctx.chN.order 50 = 252000)

end CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
