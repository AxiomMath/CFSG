module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverTop
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverMain

public section

namespace CFSG.QuasithinUnique.Ch1

theorem lemma115_3_List_proved :
    Lemma115_3_List :=
  lemma115_3_List_of_rest_inputs' K1.titsSylowCentralizingAutInner
    (sporadicRestAutInner_of_J4OutOdd Setup.X1.j4OuterOdd) titsTwoCoverTrivial

end CFSG.QuasithinUnique.Ch1
