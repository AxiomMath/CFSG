module

public import CFSG.ClassicalInvolution.Q3.TA3LiftQ8
public import CFSG.ClassicalInvolution.Q3.TL3CentTwin
public import CFSG.ClassicalInvolution.Q3.TL3EndGold

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic


theorem tightHasMember3LargeBelowQ8_of_leaves₂
    (hF1 : TightF1S fun m => CIT3Below m ∧ TightBelow m)
    (htw : ∀ n, TightTwistAllTwin n) (hsmall : TightSmallBase)
    (hliftS : ∀ n, TightLargeLiftS n) (hliftC : ∀ n, TightCentTwinLift n) :
    TightHasMember3LargeBelowQ8 := by
  have h11b :=
    tightC19_11bS_of_F1_endgame hF1
      (tightEndGameS_of_solv (tightEndGameSolv_of_odd tightEndGameOdd_holds))
  have hE := tightLargeEdgeS_of_core h11b
  exact tightHasMember3LargeBelowQ8_of_inductive₂
    (tightInductive_of_step (tightStep_of_parts₅ htw hsmall hE hliftS hliftC)) hE

end CFSG.ClassicalInvolution.Q3.TA3
