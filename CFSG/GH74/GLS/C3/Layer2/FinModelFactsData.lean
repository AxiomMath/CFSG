
module

public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataBase

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataInputs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataInputs
public import Certificates.Certificate5040
public import Certificates.Certificate5040Base

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm CFSG.GH74.GLS.C3.Layer2

namespace Facts

theorem factsProp
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) : FactsProp n := by
  rcases hn with rfl | rfl
  · exact Certificates.certificate5040.1
  · exact Certificates.certificate5040.2

end Facts

end CFSG.GH74.GLS.C3.Layer2.Model
