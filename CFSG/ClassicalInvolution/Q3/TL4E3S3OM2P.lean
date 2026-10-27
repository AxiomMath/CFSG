module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4O8A
public import Certificates.Certificate55118
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.EvenSmallLie.OmegaEight CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TL4.E4O8

namespace E3S3O


theorem sg_model {s y : Equiv.Perm (Fin 360)} (hs : s ∈ sig) (hsy : s⁻¹ * y ∈ omegaT)
    (hyu : y * u0 = u0 * y) (hyv : y * v0 = v0 * y) (hyy : y * y = 1)
    {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) (hgx : g * mainPerm 0 = mainPerm 0 * g)
    (hne : conjSub g K0 ≠ K0) {w : Equiv.Perm (Fin 360)} (hw : w ∈ conjSub g K0)
    (hact : ∀ b ∈ conjSub g K0, y * b * y⁻¹ = w * b * w⁻¹) :
    ∃ d ∈ omegaT, d * mainPerm 0 = mainPerm 0 * d ∧ conjSub d K0 ≠ K0 ∧
      ∀ b ∈ conjSub d K0, y * b = b * y :=
  Certificates.certificate55118 y ⟨s, hs, hsy⟩ hyu hyv hyy g hg hgx hne w hw hact

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
