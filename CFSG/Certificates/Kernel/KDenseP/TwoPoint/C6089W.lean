module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6089
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.ThRels
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

open CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint in
theorem CFSG.KD.TP.c6089.weq :
    wordsEqB CFSG.KD.TP.c6089.WD (CFSG.KC.KDense.Y443.words p6089) 72 = true := by
  rw [p6089, thR_eq]
  quickRfl

end
