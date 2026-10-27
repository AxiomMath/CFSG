module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8D4Main
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ExcMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem kd264F8Cls_holds : KD264F8Cls :=
  kd264F8Cls_of_pieces KD264F8ClsUni_holds KD264F8ClsOrthPlus_holds KD264F8ClsOrthMinus_holds
    KD264F8ClsExc_holds

theorem kd264F8Row_holds : KD264F8Row :=
  kd264F8Row_of_pieces kd264F8Cls_holds KD264F8KerLn_holds KD264F8KerSp_holds KD264F8KerOm_holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
