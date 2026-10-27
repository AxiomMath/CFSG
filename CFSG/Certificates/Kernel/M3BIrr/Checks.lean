module

public import CFSG.Certificates.Kernel.M3BIrr.Mats

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M3BI

open Timmesfeld.M3B CFSG.HardMathSupport.MathTwE6.M3BIrr CFSG.KC.M3BIrr

theorem powA : meq (pow2520 (matOf (LM ()) w₁)) A0 = true := by decide +kernel
theorem powB : meq (pow2520 (matOf (LM ()) w₂)) B0 = true := by decide +kernel
theorem ordA : meq (mpow A0 13) mone = true := by decide +kernel
theorem ordB : meq (mpow B0 11) mone = true := by decide +kernel
theorem idem : meq (madd (madd (polyEval (idemCoeffs.getD 0 []) A0) (polyEval (idemCoeffs.getD 1 []) A0))
    (madd (polyEval (idemCoeffs.getD 2 []) A0) (polyEval (idemCoeffs.getD 3 []) A0))) mone = true := by
  decide +kernel
theorem fac0 : meq (polyEval (idemCoeffs.getD 0 []) A0) (mmul (matCi 0) (matBi 0)) = true := by decide +kernel
theorem fac1 : meq (polyEval (idemCoeffs.getD 1 []) A0) (mmul (matCi 1) (matBi 1)) = true := by decide +kernel
theorem fac2 : meq (polyEval (idemCoeffs.getD 2 []) A0) (mmul (matCi 2) (matBi 2)) = true := by decide +kernel
theorem fac3 : meq (polyEval (idemCoeffs.getD 3 []) A0) (mmul (matCi 3) (matBi 3)) = true := by decide +kernel
theorem supp0 : suppOK 0 = true := by decide +kernel
theorem supp1 : suppOK 1 = true := by decide +kernel
theorem supp2 : suppOK 2 = true := by decide +kernel
theorem supp3 : suppOK 3 = true := by decide +kernel

end CFSG.KD.M3BI

end
