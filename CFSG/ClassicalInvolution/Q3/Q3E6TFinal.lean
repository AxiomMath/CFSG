module

public import CFSG.ClassicalInvolution.Q3.Q3E6TGraph
public import CFSG.ClassicalInvolution.Q3.Q3E6TLin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC


theorem endAdaptation3_of_productP1 (hP : Q3TC.ProductP1Input3) (hPhan : Phan3Rec) :
    EndAdaptation3 := by
  intro G _ _ _ hnab K z hR hshape c nd β hβ hn3
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  exact te6Adaptation3_of_adaptedFrames hPhan hsingle hshape c nd
    (te6AdaptedFrames3_of_isolated hsingle hshape c nd
      (te6PartnerIsolated3_of_productP1 hP hnab hR c nd hβ hn3)
      (te6NotGraphField3_of_productP1 hP hnab hR hsingle hshape c nd hβ hn3))

theorem endObstructionData3_of_productP1 (hP : Q3TC.ProductP1Input3) (hPhan : Phan3Rec) :
    EndObstructionData3 :=
  endObstructionData3_of_split (endPartnerAtX3_of_productP1 hP)
    (endAdaptation3_of_productP1 hP hPhan)

end CFSG.ClassicalInvolution.Q3.Q3E6T
