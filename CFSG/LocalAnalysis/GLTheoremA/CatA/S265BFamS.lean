module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BFourDisp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BDispDisp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBigAll
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClOm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6U6
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU5Inv
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU6Even
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265


theorem qsBRes_holds : QSBRes :=
  qsBRes_of_branches BSCl.qsBResSp10_holds BSCl.qsBResOm10m_holds BSCl.qsBResU6two_holds
    (qsBRes_twE6 TE6.twE6U6Even_holds) TE6.twE6U5Inv_holds

theorem qsFamB_holds : QSFamB :=
  qsFamB_of_high (qsFamBHigh_of_parts qsBRank_holds qsBBig_holds qsBRes_holds)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
