module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U38SylowSound
public import Certificates.Certificate211001

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB


theorem kd26d_holds : CFSG.LocalAnalysis.GLTheoremA.KD26d :=
  kd26d_of_u38MeetsX
    (u38MeetsX_of_sylow (u38SylowMeetsX_of_check Certificates.certificate211001))

end CFSG.LocalAnalysis.GLTheoremA.CatB
