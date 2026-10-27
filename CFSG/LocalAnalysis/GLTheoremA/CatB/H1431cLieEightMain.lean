module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightD4Tri
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightExc
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightF4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightRee
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightSpInn
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightTwD4
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoTwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Main


theorem lieSEight_holds : LieSEight :=
  have hLO := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hGA := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  lieSEight_of_at (lieSEightAt_of_families
    (lieSEightAt_of_noAt (lieSEightNoAt_linear hLO))
    (lieSEightAt_of_noAt (lieSEightNoAt_unitary hLO))
    (lieSEightAt_B_of_four hGA hLO (lieSEightAt_B4 hGA (lieSEightSpInner_holds hLO)))
    (lieSEightAt_D hGA hLO (lieSEightD4Tri_holds hLO))
    (lieSEightAt_twistedD hGA (lieSEightNoAt_twistedD4 hLO))
    (lieSEightAt_E hGA)
    (lieSEightAt_of_noAt (lieSEightNoAt_F4 hLO))
    lieSEightAt_twistedE6
    (lieSEightAt_of_noAt (lieSEightNoAt_reeF4 hLO))
    (lieSEightAt_of_noAt (lieSEightNoAt_other hLO)))

end Main

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
