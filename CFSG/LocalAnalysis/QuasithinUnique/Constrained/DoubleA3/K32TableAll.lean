module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL3Cover

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

theorem k32TableW_proved
    (hP : Prop121Three) (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) :
    K32TableW :=
  k32TableW_of_families hP hD h27_1 k32ExclBender_proved k32ExclPSL3_proved k32ExclPSp4_proved
    (k32ExclPSL3Cover_of_bound fun _ _ _ _ hF => k32ZBound2_l3_four hF)

end CFSG.QuasithinUnique.DoubleA3
