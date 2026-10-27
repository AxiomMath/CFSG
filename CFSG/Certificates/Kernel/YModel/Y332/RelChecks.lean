module

public import CFSG.Certificates.Kernel.YModel.Y332.Data
public import CFSG.YGroups.Defs

public section

set_option maxRecDepth 100000

namespace CFSG.KD.YMY332

open CFSG.KC.YModel CFSG.YGroups

theorem ch10099rels : relsOK 15 9 Nf (yRels 3 3 2) = true := by
  quickRfl

end CFSG.KD.YMY332

end
