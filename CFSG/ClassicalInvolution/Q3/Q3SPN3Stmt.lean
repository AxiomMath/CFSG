module

public import CFSG.ClassicalInvolution.Asc77.AscSPN10

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3SPN3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic


@[expose] def SpinGen3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), Asc77.T7P.SpinTag t n → StatedLieAdmissible t n 3 1 →
    Asc77.SPN.SpinGenOn t (modelUniv t n 3 1 Nat.prime_three)

end CFSG.ClassicalInvolution.Q3.Q3SPN3
