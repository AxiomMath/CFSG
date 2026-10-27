module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def pairsN (LN : List M) (t : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹)) ||
      (memB LN a && memB LN b) ||
      C.any fun x => decide (x ^ 3 = 1) && !decide (x * a = a * x ∧ x * b = b * x) &&
        C.all fun y => !decide (y * a = a * y ∧ y * b = b * y) || decide (x * y = y * x)

end CFSG.ClassicalInvolution.Q3.TA3.Check
