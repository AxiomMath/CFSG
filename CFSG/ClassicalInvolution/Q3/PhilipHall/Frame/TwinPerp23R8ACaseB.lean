module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ACaseBQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ACaseBMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


theorem p23E8ACaseB_of_thmEQ8 {n : ℕ} (hE : TwinThmEW.ThmEQ8) : P23E8ACaseB n := by
  intro hcit hP Y _ _ R S t K' W u e g hc _ hA5 _ hαb y hyY hyt hy3 hye hB
  exact CaseB.false_of_rLayer_te_le_centralizer_ue hc
    (CaseB.rLayer_te_le_centralizer_ue hE hcit hP hc hA5 hαb hyY hyt hy3 hye hB
      (CaseB.rLayer_u_le_normalizer hE hcit hP hc hA5 hαb hyY hyt hy3 hye hB))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
