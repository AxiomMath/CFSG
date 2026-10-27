module

public import CFSG.CGT.Foote82.T66.CitedL13
public import CFSG.CGT.Foote82.T66.OmegaSixModel
public import Certificates.Certificate919002

public section

namespace CFSG.CGT.Foote82.OmegaSix

theorem foxCheck_holds : foxCheck () = true :=
  Certificates.certificate919002

end CFSG.CGT.Foote82.OmegaSix

namespace CFSG.CGT.Foote82

open Matrix OmegaSix

theorem h1OmegaMinusSix_holds :
    H1OmegaMinusSix := by
  intro F hF
  exact FoxH1.coboundary_of_foxCheck2 (fun _ u v => mulVec_add _ u v)
    (fun x y v => by rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec])
    (fun v => by rw [Subgroup.coe_one, Units.val_one, one_mulVec]) isVecCode isActArr_gen6
    closure_gen6 relators_spec foxCheck_holds F hF

end CFSG.CGT.Foote82
