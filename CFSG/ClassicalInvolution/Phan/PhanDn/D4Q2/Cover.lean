
module

public import CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.CoverBase
import all CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.CoverBase

public import Certificates.Certificate709441
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoComparison
import all CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph

public section

namespace CFSG.ClassicalInvolution.PhanDn.D4Q2

open CFSG.ClassicalGroups.Unitary CFSG.Sporadic.SuzRecog
open CFSG.Sporadic.SuzRecog.ElimCert

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

theorem compGraph_connected_triangulable (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) :
    (compGraph σ).Connected ∧ CFSG.Monster.B.Recog.Triangulable (compGraph σ) :=
  Certificates.certificate709441 hσ hK

theorem flagGraph_three_connected_triangulable (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) :
    (flagGraph σ 3).Connected ∧ CFSG.Monster.B.Recog.Triangulable (flagGraph σ 3) :=
  flagGraph_three_of_compGraph hσ hK (compGraph_connected_triangulable hσ hK).1
    (compGraph_connected_triangulable hσ hK).2

end CFSG.ClassicalInvolution.PhanDn.D4Q2
