
module

public import CFSG.GF2Type.Smith1979.IdxFourModelTrvBase

public import Certificates.Certificate17604

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol

theorem card_centralizer_x0 :
    Nat.card ↥(M0 ⊓ Subgroup.centralizer {x0}) = 311040 :=
  Certificates.certificate17604

end CFSG.GF2Type.Smith1979.IdxFour
