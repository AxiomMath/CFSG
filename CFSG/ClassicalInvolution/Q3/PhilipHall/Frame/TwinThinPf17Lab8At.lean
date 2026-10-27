module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinAt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf15Supply

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

theorem thinTwinLab8At_of_t4 {n : ℕ} (h4 : Thm4RTwinBelow 3 n) : ThinTwinLab8At n := by
  intro G _ _ hG K₀ K K' z π g S hS hnab hodd J α h b hlab
  exact S.twinLab8_core (S.f7Cent h4 hG hS hnab (by norm_num) J hodd) J hlab

section Proved


theorem thinTwinLab8At_proved {n : ℕ} (hA : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    ThinTwinLab8At n :=
  thinTwinLab8At_of_t4 (TwinThmEW.t4Supply_of_twoClass n hA hP)

end Proved

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin
