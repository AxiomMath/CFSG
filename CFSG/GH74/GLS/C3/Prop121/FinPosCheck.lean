module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabLemmas
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTab
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
public import CFSG.GH74.GLS.C3.Prop121.FinPosCheckInputs
public meta import CFSG.GH74.GLS.C3.Prop121.FinPosCheckInputs
public import Certificates.Certificate5089

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

theorem claimPosB6 : (mkTab 6).claimPosB = true :=
  Certificates.certificate5089.1

theorem claimPosB7 : (mkTab 7).claimPosB = true :=
  Certificates.certificate5089.2

end CFSG.GH74.GLS.C3.Layer2.Model
