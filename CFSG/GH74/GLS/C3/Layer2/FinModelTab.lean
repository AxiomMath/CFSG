module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelTabInputs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTabInputs
public import Certificates.Certificate5041

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

namespace Tab

variable {n : ℕ} [NeZero n] (t : Tab n)

@[expose] def cls3 (i : Fin 64) : ℕ := if i = t.one then 0 else if t.mulT i i = t.one then 1 else 2

end Tab

theorem validB6 : (mkTab 6).validB = true :=
  Certificates.certificate5041.1


theorem validB7 : (mkTab 7).validB = true :=
  Certificates.certificate5041.2

end CFSG.GH74.GLS.C3.Layer2.Model
