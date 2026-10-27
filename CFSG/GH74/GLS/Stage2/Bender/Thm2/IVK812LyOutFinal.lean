module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyOutMain
public import CFSG.Sporadic.Recognition.McLNoThreeCert

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open CFSG.Sporadic.Recognition.McLAS

theorem lyThreeAOuter_thm :
    LyThreeAOuter :=
  lyThreeAOuter_of_mcl mclNoThreeNormalized_of_certs

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
