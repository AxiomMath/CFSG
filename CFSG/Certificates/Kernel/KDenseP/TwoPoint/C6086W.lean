module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6086
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.ThRels
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

open CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint in
theorem CFSG.KD.TP.c6086.weq :
    wordsEqB CFSG.KD.TP.c6086.WD (CFSG.KC.KDense.Y443.words p6086) 18 = true := by
  rw [p6086, thR_eq]
  quickRfl

end
