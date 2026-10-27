module

public import CFSG.GH74.E2.SD16CertInputs
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Semidihedral
section SD16Facts

@[expose] def IsCentralInv16 (x : SD16M) : Prop := (∀ w, w * x = x * w) ∧ x * x = 1

end SD16Facts


end CFSG.GH74.E2
