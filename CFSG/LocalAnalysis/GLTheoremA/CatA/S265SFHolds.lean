module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5URes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF7
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGLinAsm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmMRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGU38
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGU6c
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniMod

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

theorem qsFamF_of_t171_noAct (hShape : T171.T171ShapeFact) (hNoAct : T171.T171NoActFact) :
    QSFamF :=
  qsFamF_of_low SF5U.qsFamF5U_holds
    (qsFamF3_of_parts
      (qsF3Gen_of_res qsF3ResF4_holds SG.qsF3ResU6_holds
        (qsF3ResCls_of_parts qsF3ResLin_holds qsF3ResUni_holds qsF3ResSp_holds qsF3ResOmP_holds
          qsF3ResOmM_holds))
      (qsF3U38_of_t171_noAct hShape hNoAct))

end CFSG.LocalAnalysis.GLTheoremA.S265

end
