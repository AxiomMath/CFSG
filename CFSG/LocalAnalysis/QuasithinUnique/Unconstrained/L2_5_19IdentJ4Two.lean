module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentJ4
public import CFSG.Sporadic.J4.QT2LocMain

public section

namespace CFSG.QuasithinUnique.Id2519.J4Row

theorem centralizerCore_one
    : CentralizerCore 1 :=
  CFSG.Sporadic.J4.QT2.constrained_centralizer_eta_one

theorem tabIdent_of_core3
    (hodd : Ch1.J4OutOdd) (h3 : CentralizerCore 3) : TabIdent :=
  tabIdent_of_j4Core hodd centralizerCore_one h3

end CFSG.QuasithinUnique.Id2519.J4Row
