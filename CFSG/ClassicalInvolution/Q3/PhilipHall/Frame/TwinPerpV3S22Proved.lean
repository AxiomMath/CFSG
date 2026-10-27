module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertBTA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3


theorem twinPerpV3E_proved
    (n : ℕ) (hA : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) : TwinPerp.TwinPerpV3E n :=
  twinPerpV3E_of_triFin TwinPerpV3.A6S.ae6TriFin_proved n hA hP

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
