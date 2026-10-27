module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Check

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def q16At (t : M) (C : List M) : Bool :=
  (C.filter fun x => decide (x ^ 4 = t)).all fun x =>
    (C.filter fun y => decide (y * y = t)).all fun y => !decide (y * x = x⁻¹ * y)

@[expose] def noQ16Check (L reps : List M) : Bool :=
  coverB reps L && reps.all fun t => q16At t (centB L t)

end CFSG.CGT.PushingUpLit.SolKNA.R4.Check
