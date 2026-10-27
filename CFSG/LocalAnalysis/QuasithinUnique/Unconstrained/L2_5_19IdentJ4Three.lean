module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentJ4Two
public import CFSG.Sporadic.J4.QT2AMain

public section

namespace CFSG.QuasithinUnique.Id2519.J4Row

theorem centralizerCore_three
    : CentralizerCore 3 :=
  CFSG.Sporadic.J4.QT2A.constrained_centralizer_eta_three

theorem tabIdent_of_outOdd
    (hodd : Ch1.J4OutOdd) : TabIdent :=
  tabIdent_of_core3 hodd centralizerCore_three

end CFSG.QuasithinUnique.Id2519.J4Row
