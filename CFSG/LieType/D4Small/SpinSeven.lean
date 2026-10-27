module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel

public section

namespace CFSG.LieType.D4Small

open CFSG.StandardType CFSG.StandardType.Triality

@[expose] noncomputable def spinSeven (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (Om8 K) :=
  (MonoidHom.eqLocus (AutOm.plusRefl (K := K) one_le_four).toMonoidHom
    (MonoidHom.id (Om8 K))).map (theta : MulAut (Om8 K)).toMonoidHom

end CFSG.LieType.D4Small
