module

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
public import Certificates.Certificate5051

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

@[expose] def sh0M :
    List ↥Sh0 := Sh0L.pmap (fun p hp => (⟨p, hp⟩ : ↥Sh0)) (fun _ h => h)

@[expose] def sh0Code (m : ↥Sh0) : Nat := codeP16 m.1

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
