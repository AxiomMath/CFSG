module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL2p
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL42
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMathieu

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

theorem k32TableW_of_families
    (hP : Prop121Three) (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (h1 : K32ExclBender) (h2 : K32ExclPSL3) (h3 : K32ExclPSp4)
    (h4 : K32ExclPSL3Cover) : K32TableW :=
  k32TableW_of_inputs hP hD h27_1
    (k32AutExcl_of_families h1 h2 h3 h4 k32ExclPSL2p_proved k32ExclM22_proved
      k32ExclM22Cover_proved k32ExclM23_proved k32ExclPSL42_proved)
    k32AltOut_proved

end CFSG.QuasithinUnique.DoubleA3
