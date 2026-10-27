module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3

@[expose] def LowerClassR (r n : ℕ) : Prop :=
  (∀ r' : ℕ, 4 ≤ r' → r' < r → TightBelowR r' n) ∧ TL4.TightBelowRPlus 3 n

end CFSG.CGT.PushingUpLit.SolKNA.R4
