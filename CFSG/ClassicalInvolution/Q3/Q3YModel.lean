module

public import CFSG.ClassicalInvolution.Q3.Q3ExcCenterE6
public import CFSG.ClassicalInvolution.Q3.Q3ExcCenterD4
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank

namespace Q3Y

theorem center_modelUniv_eq_bot_of_tag {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E8 ∨ t = .trialityD4 ∨ t = .twistedE6)
    (hadm : StatedLieAdmissible t n 3 1) :
    Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥ := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  · exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  · exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  · exact exc3_center_trialityD4 n Nat.prime_three
  · obtain rfl : n = 0 := hadm.2.2
    exact exc3_center_twistedE6_model Nat.prime_three

end Q3Y

end CFSG.ClassicalInvolution.Q3
