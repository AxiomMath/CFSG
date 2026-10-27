module

public import CFSG.Certificates.Kernel.Common.LceS

public section

namespace CFSG.KC.LceSR

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop

@[expose] noncomputable def idsChunk (WT : Nat → Nat) (m C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) S)
      (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        strictN (WT id) (fun w =>
          ih (Nat.shiftRight J (jLen J w))
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runIds (WT : Nat → Nat) (m : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (idsChunk WT m C S) ih) Cs

@[expose] noncomputable def wtPer0 (WT : Nat → Nat) (m P : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun h ih => andB
    (Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB
      ((fun k => orB (Nat.beq (WT k) (nat_lit 0))
          (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P)))))
        (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2)
      (nat_lit 256)) ih) (nat_lit 256)

end CFSG.KC.LceSR

end
