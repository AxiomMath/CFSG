
module


public import Certificates.Certificate12636

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.HeldB
open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert

theorem heThree_counts :
    ((countWPar 1 (commB heThreeBA heBase)
        (heBlock0.filter fun t0 => heThreeBA[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 7560 &&
      countWPar 1 (commB heThreeBB heBase)
        (heBlock0.filter fun t0 => heThreeBB[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 504 &&
      countWPar 1 (fun w => fixB heBase w 3) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 12609) = true) :=
  Certificates.certificate12636

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

end
