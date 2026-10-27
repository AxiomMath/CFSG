module

public import CFSG.ClassicalInvolution.Q3.Q3TIVMain
public import CFSG.ClassicalInvolution.Q3.Q3TIVOr2
public import CFSG.ClassicalInvolution.Q3.Q3TIVSm1
public import CFSG.ClassicalInvolution.Q3.Q3TIVSm2

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinRow)


theorem twinProductCentral3_of_row {t : StatedLieTag} {n : ℕ} (hrow : TwinRow t n) :
    TwinProductCentral3 t n := by
  rcases hrow with ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ |
    ⟨-, rfl, rfl⟩
  · exact twinProductCentral3_plus hn
  · exact twinProductCentral3_psl4
  · exact twinProductCentral3_odd hn
  · exact twinProductCentral3_psp2
  · exact twinProductCentral3_minus hn
  · exact twinProductCentral3_psu4

theorem twinInvolution3_of_odd3 (h3 : OddThreeFreeInput) : Q3TY.TwinInvolution3 := by
  intro G _ _ _ hnab K z hR t n hrow hshape T hT
  exact twinInvolutionRow3 (twinRowFacts3_of_row hrow) (twinProductCentral3_of_row hrow) h3 hnab
    hR hshape hT

end CFSG.ClassicalInvolution.Q3.Q3TIV
