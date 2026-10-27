module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6087
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.ThRels
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

open CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint in
theorem CFSG.KD.TP.c6087.weq :
    wordsEqB CFSG.KD.TP.c6087.WD (CFSG.KC.KDense.Y443.words p6087) 18 = true := by
  rw [p6087, thR_eq]
  quickRfl

end
