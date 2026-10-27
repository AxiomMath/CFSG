module

public import CFSG.Certificates.Kernel.Common.HOrb
public import CFSG.Certificates.Kernel.Co2.Bound3.F7

public section

namespace CFSG.KC.Co2K

open CFSG.KC CFSG.KC.Loop CFSG.KC.HOrb CFSG.KC.LceS

@[expose] noncomputable def evalE (FS : Nat → Nat) (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE7
    (fun q acc => strictN acc (fun x => mul7 x (FS (Nat.shiftRight (byte (wWord w) q) (nat_lit 1))))) (wLen w)

@[expose] noncomputable def invol7 (X : Nat) : Bool := andB (wf7 X) (Nat.beq (mul7 X X) ONE7)

end CFSG.KC.Co2K

end
