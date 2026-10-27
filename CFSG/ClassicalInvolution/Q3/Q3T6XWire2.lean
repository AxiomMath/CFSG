module

public import CFSG.ClassicalInvolution.Q3.Q3T6XTwin
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Plug
public import CFSG.ClassicalInvolution.Q3.Q3MTShapes
public import CFSG.ClassicalInvolution.Q3.Q3DInputs3
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.ClassicalInvolution.Q3.Q3T6DAEmpty
public import CFSG.ClassicalInvolution.Q3.Q3T6DVFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Uniform


theorem aEmptyDU_three_of_fusionMinTwin (h : Fusion3MinBranchTwin) : AEmptyDU 3 1 :=
  Q3T6D.aEmptyDU_three_of_hyp51At (hypOmegaModDU_three_of_fusionMinTwin h)
    ComponentClassification.RankTwoFoundation.asc75Theorem4
    (fun _ hn => ih8T_of_rest ihInterfaceU_three
      (ih8RestU_three_of ih8G2D4EdgeU_proved ih8ThreeU_proved ih8TwinShapeU_proved
        (fun _ hn => Disc3.thm5BelowU_three_of_nonGen
          (thm5NonGenBelowU_of_twin Disc3.twinGen3_proved hn) hn)
        Q3MT.muTable_three thm3_proved) hn)
    Q3T6D.res20_7Hyp51AtThree_proved' Q3T6D.res10bP1_proved3

theorem aEmptyDU_three_of_fusionMin (h : Fusion3MinBranch) : AEmptyDU 3 1 :=
  aEmptyDU_three_of_fusionMinTwin (fusion3MinBranchTwin_of_branch h)

end CFSG.ClassicalInvolution.Q3.Q3T6X
