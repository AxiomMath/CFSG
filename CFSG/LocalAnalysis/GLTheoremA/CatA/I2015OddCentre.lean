module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

theorem i2015OddCentreFact_holds : I2015OddCentreFact :=
  fun _ _ _ _ _ hp hp2 _ _ _ _ =>
    CFSG.LocalAnalysis.GLTheoremB.odd_card_center hp hp2 (CFSG.pPrimeCore_quotient_eq_bot hp)

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
