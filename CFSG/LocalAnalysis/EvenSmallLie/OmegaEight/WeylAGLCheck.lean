module

public import Certificates.Certificate3190

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

theorem agl_frames (a b d e : Fin 8) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (he : (planeThrough a b d).testBit e = false) :
    ∃ τ ∈ Subgroup.closure frameGens, τ 0 = a ∧ τ 1 = b ∧ τ 2 = d ∧ τ 4 = e :=
  Certificates.certificate3190.1 a b d e hab had hbd he

theorem frame16_check : frame16Check = true :=
  Certificates.certificate3190.2

end CFSG.EvenSmallLie.OmegaEight.Weyl
