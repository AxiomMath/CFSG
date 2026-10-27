module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6090
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.ThRels
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

open CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint in
theorem CFSG.KD.TP.c6090.weq :
    wordsEqB CFSG.KD.TP.c6090.WD (CFSG.KC.KDense.Y443.words p6090) 60 = true := by
  rw [p6090, thR_eq]
  quickRfl

end
