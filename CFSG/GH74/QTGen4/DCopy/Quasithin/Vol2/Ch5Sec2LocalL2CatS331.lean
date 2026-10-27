module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Two
public import CFSG.Quasithin.H13.NQCatL2LieParabolic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_L2Gen_of_cat_F4 (h510 : Stmt5_1_10_F4) : Stmt5_2_L2Gen_F4 :=
  stmt5_2_L2Gen_of_F4 NQCat.factL2LieParabolic_holds h510

theorem stmt5_2_6_borel_of_cat_F4 (hLie : Stmt5_2_L2Lie_F4) (h510 : Stmt5_1_10_F4) : Stmt5_2_6_borel_F4 :=
  stmt5_2_6_borel_of_F4 NQCat.factL2LieParabolic_holds hLie h510

theorem stmt5_2_L2Lie_of_inputs_cat_F4
    (hU3 : FactU3Cover) (hRL : RankOneListedFacts.{0}) (h515 : Stmt5_1_5_F4) (h510 : Stmt5_1_10_F4) :
    Stmt5_2_L2Lie_F4 :=
  stmt5_2_L2Lie_of_inputs_F4 hU3 NQCat.factL2LieParabolic_holds hRL h515 h510

theorem stmt5_2_6_borel_of_inputs_cat_F4
    (hU3 : FactU3Cover) (hRL : RankOneListedFacts.{0}) (h515 : Stmt5_1_5_F4) (h510 : Stmt5_1_10_F4) :
    Stmt5_2_6_borel_F4 :=
  stmt5_2_6_borel_of_cat_F4 (stmt5_2_L2Lie_of_inputs_cat_F4 hU3 hRL h515 h510) h510

end CFSG.Quasithin.H13
