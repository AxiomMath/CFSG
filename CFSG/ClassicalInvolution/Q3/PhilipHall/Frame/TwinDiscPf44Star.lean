module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf43Disc15Z
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf42Disc15

public section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


theorem twinDiscPerpSPAll_of_y14ConnStar
    (hLEnd : CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafEnd 3
      (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3))
    (hstar : ∀ n, CIT3Below n → CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n →
      TwinDisc.Disc14YConnStar n) :
    ∀ n, TwinCoreDiscPerpSP n :=
  twinDiscPerpSPAll_of_disc15T hLEnd fun n hA hP =>
    TwinDisc.disc15T_of_y14ConnT hA hP (TwinThmEW.t4Supply_of_twoClass n hA hP)
      (TwinDisc.disc14YConnT_of_star (hstar n hA hP))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
