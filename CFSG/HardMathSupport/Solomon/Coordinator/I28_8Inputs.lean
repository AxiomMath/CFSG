module

public import Mathlib
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.L34Inputs
public import CFSG.GH74.KGroups.L34AutInputs
public meta import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.GH74.KGroups.L34Inputs
public meta import CFSG.GH74.KGroups.L34AutInputs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Sporadic.Schreier

@[expose] def l34SevenCheck (_ : Unit := ()) : Bool :=
  let l7 := (elemsT QP).filter (fun q => orderIs q 7)
  (elemsT QA).all fun a =>
    decide (a * a ≠ 1) || QP.sift a 0 ||
      l7.any (fun q => decide (a * q = q * a) || decide (a * q * a⁻¹ = q⁻¹))

end CFSG.HardMathSupport.Solomon.Coordinator
