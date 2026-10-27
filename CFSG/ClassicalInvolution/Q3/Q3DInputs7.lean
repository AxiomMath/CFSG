module

public import CFSG.ClassicalInvolution.Q3.Q3DInputs3
public import CFSG.ClassicalInvolution.Q3.Q3MTShapes

public section

namespace CFSG.ClassicalInvolution.Q3.Disc3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform

theorem ih8T_three_proved : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n := fun _ hn =>
  ih8T_of_rest ihInterfaceU_three
    (ih8RestU_three_of ih8G2D4EdgeU_proved ih8ThreeU_proved ih8TwinShapeU_proved
      (fun _ hn => thm5BelowU_three_of_nonGen (thm5NonGenBelowU_of_twin twinGen3_proved hn) hn)
      Q3MT.muTable_three thm3_proved) hn

end CFSG.ClassicalInvolution.Q3.Disc3
