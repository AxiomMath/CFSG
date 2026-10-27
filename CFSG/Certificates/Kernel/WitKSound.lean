module

public import Certificates.Data.Kernel.Misc.WitK
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.ClassicalInvolution.Q3.Q3SWCheck

public section

namespace CFSG.KC.WitK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

theorem witnessCheckA_PP {n w P Q Z : Nat} (hsz : szOK n w = true) (hP : PP n w P)
    (hQ : PP n w Q) (hZ : PP n w Z) :
    CFSG.ClassicalInvolution.Q3.witnessCheckA n (unpack n w P) (unpack n w Q) (unpack n w Z) =
      witK n w P Q Z := by
  have hPQ := hP.mul hQ
  have hI := PP.id hsz
  unfold CFSG.ClassicalInvolution.Q3.witnessCheckA CFSG.ClassicalInvolution.Q3.cubeIdA witK
  rw [idA_eq hsz, compA_PP hP hP, compA_PP hP (hP.mul hP), compA_PP hQ hQ,
    compA_PP hQ (hQ.mul hQ), compA_PP hP hQ, compA_PP hPQ hPQ,
    eqA_PP (hP.mul (hP.mul hP)) hI, eqA_PP (hQ.mul (hQ.mul hQ)) hI, eqA_PP (hPQ.mul hPQ) hI,
    eqA_PP hPQ hI, eqA_PP hPQ hZ]

end CFSG.KC.WitK

end
