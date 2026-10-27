module

public import CFSG.Certificates.Kernel.McL.Sub

public section

namespace CFSG.KC.McL.RangeX

open CFSG.KC CFSG.KC.McL

@[expose] noncomputable def smallTabB (F : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c acc => andB acc
    (andB (Nat.blt (Sub.pn (F c)) (nat_lit 16))
      (Nat.blt (Sub.pw (F c)) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (Sub.pn (F c)))))))
    (nat_lit 256)

@[expose] noncomputable def xtLt (F : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c acc => andB acc
    (Nat.rec (motive := fun _ => Bool) true (fun i acc2 => andB acc2
      (Nat.blt (wLet (Sub.pw (F c)) i) (nat_lit 254))) (Sub.pn (F c)))) (nat_lit 256)

@[expose] noncomputable def entsBelow (T : Nat → Nat) (nE b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r acc => andB acc
    (Nat.rec (motive := fun _ => Bool) true (fun i acc2 => andB acc2
      (Nat.blt (wLet (LceS.wWord (T r)) i) b)) (LceS.wLen (T r)))) nE

@[expose] noncomputable def epWrap (EP ED : Nat → Nat) (nE P : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun h ih => andB
    (Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB
      ((fun e => orB (Nat.beq (EP e) (nat_lit 0))
          (andB (Nat.blt (Nat.mod e P) nE) (andB (Nat.beq (EP e) (EP (Nat.mod e P)))
            (Nat.beq (ED e) (ED (Nat.mod e P))))))
        (Nat.add (Nat.shiftLeft h (nat_lit 6)) l)) ih2)
      (nat_lit 64)) ih) (nat_lit 64)

end CFSG.KC.McL.RangeX

end
