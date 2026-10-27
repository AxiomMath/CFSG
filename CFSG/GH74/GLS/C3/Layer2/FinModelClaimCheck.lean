
module

public import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTab
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
public import Certificates.Certificate5038

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

theorem claimB6 : (mkTab 6).claimB = true :=
  Certificates.certificate5038.1

theorem claimB7 : (mkTab 7).claimB = true :=
  Certificates.certificate5038.2

end CFSG.GH74.GLS.C3.Layer2.Model
