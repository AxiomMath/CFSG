module

public import CFSG.Certificates.Kernel.Common.DceS
public import CFSG.Certificates.Kernel.Co1.Data.D1S_0
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.D1S

theorem sH0 : CFSG.KC.DceS.constOK OMT NB NO I0 BB BASEM NL TL ND ALIVE = true := by
  quickRfl

theorem sH1 : CFSG.KC.DceS.invSelfOK INV INV8 NL = true := by
  quickRfl

theorem sH2 : CFSG.KC.DceS.invRelOK RT NL NR IH = true := by
  quickRfl

theorem sH3 : CFSG.KC.Loop.allBelow NL (nat_lit 1) (CFSG.KC.DceS.letOK LT TL) = true := by
  quickRfl

theorem sH4 : CFSG.KC.Loop.allBelow NH (nat_lit 27) (CFSG.KC.DceS.hdrOK HT LT NL) = true := by
  quickRfl

theorem sH5 : CFSG.KC.Loop.allBelow NO (nat_lit 27) (CFSG.KC.DceS.omOK PBT OMT GT HT NB NH (PBT I0))
    = true := by
  quickRfl

theorem sH6 : CFSG.KC.DceS.wordsOK WT RT LT INV INV8 NL TL NR NW HS = true := by
  quickRfl

theorem sH7 : CFSG.KC.Loop.allBelow NR (nat_lit 1) (CFSG.KC.DceS.relOK RT LT NL TL) = true := by
  quickRfl

end CFSG.KD.D1S

end
