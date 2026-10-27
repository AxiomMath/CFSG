
module

public import CFSG.GH74.GLS.C3.Layer2.L5C2fTableInputsBase

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C2fInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2fInputs
public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import Certificates.Certificate5056
public import Certificates.Certificate5065Base

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

theorem sh0_chk :
    tabCheck sh0M sh0Code (buildTab sh0M sh0Code) (buildInv sh0M sh0Code)
    (buildOne sh0M sh0Code) = true :=
  Certificates.certificate5056

@[expose] def sh0D : TabData ↥Sh0 :=
  mkTabData sh0M sh0Code sh0M_complete (buildTab sh0M sh0Code) (buildInv sh0M sh0Code)
    (buildOne sh0M sh0Code) sh0_chk

@[expose] def eng0 :
    Eng sh0D.n := engOf sh0D embHom0

@[expose] def isR1
    (u : Idx sh0D.n) : Bool := R1L.contains (sh0D.e u).1

@[expose] def chk0 :
    Bool :=
  letI := sh0D.grp
  engOK eng0 && decide (survivors eng0 = [[0, 1, 1, 0, 0, 1]]) &&
    eng0.invs.all fun u => eng0.invs.all fun v =>
      !isR1 u || !decide (blkOf eng0.ciA [0, 1, 1, 0, 0, 1] u = blkOf eng0.ciA [0, 1, 1, 0, 0, 1] v) ||
        isR1 v

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
