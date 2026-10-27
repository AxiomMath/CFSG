module

public import CFSG.GH74.QTGen4.Leaves.Ident1277
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13 CFSG.Open

theorem stmt12_7_1_F4_holds : Stmt12_7_1_F4 := by
  intro G _ _ T L V hs hna hq hT hnot hmax hfaith hquasi hnorm hirr hA6
  exact (false_of_hyp1271_gen4 Finite4.gen4
    ⟨⟨hs, hna, hq, hT, hnot, hmax, hfaith, hquasi, hnorm, hirr⟩, hA6⟩).elim

end CFSG.GH74.QTGen4.Leaves
