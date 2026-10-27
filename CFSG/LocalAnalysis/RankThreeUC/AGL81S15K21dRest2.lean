module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dRed
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dSimple
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA6
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Holds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dU3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsHolds

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section Rest2


theorem K21dRes_of_rest2 (h : K21dGeomU42 ∧ K21dGeomL5) : K21dRes :=
  ⟨k21dSimple_holds, K21dGeom_of_families k21dGeomTits_holds h.1 h.2 k21dGeomA8_holds
    k21dGeomA6_holds k21dGeomU3_holds⟩

end Rest2

end CFSG.LocalAnalysis.RankThreeUC.S15
