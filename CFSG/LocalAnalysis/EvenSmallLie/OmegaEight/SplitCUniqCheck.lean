module

public import Certificates.Certificate3560
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

theorem uniqPlus_check :
    ∃ W : UniqWit, W.J = 38 ∧ W.y = yIdx ∧ W.cl = (fun i => (invW i).1) ∧
      uniqCheckW 8192 commP conjP invP W = true :=
  Certificates.certificate3560.1

theorem uniqMinus_check :
    ∃ W : UniqWit, W.J = 36 ∧ W.y = OmegaEightMinus.yIdx ∧
      W.cl = (fun i => (OmegaEightMinus.invW i).1) ∧
      uniqCheckW 8192 OmegaEightMinus.commM OmegaEightMinus.conjM OmegaEightMinus.invM W = true :=
  Certificates.certificate3560.2

end CFSG.EvenSmallLie.OmegaEight.SplitC
