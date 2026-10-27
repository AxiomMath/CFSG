module

public import CFSG.GH74.GLS.Prop27.LocBal
public import CFSG.GH74.KGroups.M11
public meta import CFSG.GH74.GLS.Prop27.LocBal
public meta import CFSG.GH74.KGroups.M11
public import Certificates.Certificate5097
public import Certificates.Certificate5125
public meta import CFSG.Assembly.BalancedOddCoreCompletion
public import CFSG.Assembly.BalancedOddCoreCompletion
public meta import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.Assembly.CompletedOddCoreElimination
public meta import CFSG.Fischer.Uniq.CompTau
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.E2.ComponentsShape
public meta import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.GLS.Statements
public meta import CFSG.GH74.GLS.Statements
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public meta import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public meta import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.SignalizerFunctor
public meta import CFSG.Walter.J1
public import CFSG.Walter.J1
public meta import Certificates.Certificate5007
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG.GH74.KGroups CFSG.GH74.E2 CFSG.Certificates

theorem m11_oddCore_check :
    oddCoreCheck 495 (elemsT M11.Q) (elemsT M11.Q) = true :=
  Certificates.certificate5097

theorem locBal2_M11 :
    LocBal2 ShapeM11 :=
  locBal2_of_chains ShapeM11 M11.Q M11.Q M11.Q_ok M11.Q_ok le_rfl (a := 4) (m := 495)
    (by decide) (by rw [card_group M11.Q M11.Q_ok, M11.Q_valid.2]; norm_num) (fun _ _ h => M11.autModel h)
    m11_oddCore_check

end CFSG.GH74.GLS.Prop27
