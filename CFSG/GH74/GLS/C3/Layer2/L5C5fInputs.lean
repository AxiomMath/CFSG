module

public import CFSG.GH74.GLS.C3.Layer2.L5C5g
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5e
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5g
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5065
public import Certificates.Certificate5066

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

@[expose] def sh2Eng
    (ty : Fin 4) : Eng (sh2TabD ty).n := engOf (sh2TabD ty) ((inc ty).comp embHom0)

@[expose] def sh2EngChk
    (ty : Fin 4) : Bool :=
  letI := (sh2TabD ty).grp
  engOK (sh2Eng ty) && decide (survivors (sh2Eng ty) = [])

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
