module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9LemEProof
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9TypesOf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9EndMain

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

theorem sixFiveNoE9_of_leaves_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h116 : AS116Statement)
    (h1416 : StageLemma1416) (h15 : StageLemma1515CE) (h19s : StageLemma1519)
    (h113 : StageLemma15113) (h14 : StageLemma15114)
    (nLJ : Input15120LJ) (nB42 : Input15120B42List) (nA : Input15120L2Block)
    (nB : Input15120RankTwoExcl) (nC : Input15120L45) (nD : Input15120TwoB_F4)
    (nCL : Input15120CompListCoarse) (mA : Input15120MLA) (mB : Input15120MLB)
    (hcutB : TypeCutBlock1521) (hcutC : TypeCutComp1521) (hcutAlt : TypeCutCompAlt1521)
    (hFam : FamE9) (rows : H23P4.P4Rows) (h118 : TheoremC118) (h126 : TheoremC126) :
    SixFiveNoE9_F4 :=
  have hT := lemma15120TypesInput_of_F4 h1416 h15 nLJ nB42 nA nB nC nD nCL mA mB
  sixFiveNoE9_of_inputs_F4 h37 h38 h116 h15 h19s h113 h14 hT
    (lemma15121E9_of_F4 (struct15121E9_of h37 h38 hcutB hcutC hcutAlt hFam) hT h15 h19s h14 h113)
    (lemma15123FiveInputC_of_rows rows h118 h126 h37 h38)

end CFSG.Quasithin.E9
