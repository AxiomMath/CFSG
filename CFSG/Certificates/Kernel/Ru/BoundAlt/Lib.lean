module

public import Init

public section

namespace CFSG.KC.RuBA

@[expose] noncomputable def shiftF (f : Nat → Nat) (o : Nat) : Nat → Nat := fun i => f (Nat.add i o)

end CFSG.KC.RuBA

end
