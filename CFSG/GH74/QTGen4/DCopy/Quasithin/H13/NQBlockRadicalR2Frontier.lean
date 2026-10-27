module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQBlockRadicalR2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11SecOE3K
public import CFSG.Quasithin.Vol2.Ch3T313C

public section

namespace CFSG.Quasithin.H13.NQBlock

open CFSG.Open CFSG.QuasithinUnique

theorem stmt3_2_14_of_frontier_F4
    (hFSU : Vol2.Ch10.StmtFSUChoice) (h701 : Stmt7_0_1_F4) (hList : Vol2Native.A312ListFactsCat)
    (h316 : Theorem316Statement) : Stmt3_2_14_F4 :=
  stmt3_2_14_of_F4
    (Vol2.Ch11.OE3.noOddLinear_of_F4 Vol2Native.a37ForSQTKCat_proved
      (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
        Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved) hFSU h701)
    (lemma3_2_13Consumed_of h316 U3.uniqueThreeCaseModelReduction_holds)
    (Vol2.Ch11.OE4.lemma3_2_14HomocyclicConsumed_of h316 U3.uniqueThreeCaseModelReduction_holds)
    hList

end CFSG.Quasithin.H13.NQBlock
