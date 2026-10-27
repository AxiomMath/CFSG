module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycExcTwisted

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem kd264OutCyc_holds :
    KD264OutCyc :=
  kd264OutCyc_of_families lieOutCyc_linear lieOutCyc_unitary lieOutCyc_classicalBCD
    lieOutCyc_triality lieOutCyc_excUntwisted lieOutCyc_excTwisted

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
