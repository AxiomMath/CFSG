module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def nqAt (inX : M → Bool) (t : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
        (inX a && inX b && C.all fun c => !inX c ||
          (memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹)))

@[expose] def nqCheck (inX : M → Bool) (L reps : List M) : Bool :=
  coverB reps L && reps.all fun t => nqAt inX t (centB L t)

@[expose] def firstBlock (m : Equiv.Perm (Fin 24)) : Bool := decide ((m 0).val < 12)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM
