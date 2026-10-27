module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ATriGlue
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQSA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.LocalAnalysis.GLTheoremA


theorem qsFamA_holds : S265.QSFamA :=
  qsFamA_of_parts ivLieRow_holds fun h hJ hout => QSNL.false_of_d4two_outer h hJ hout

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
