module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def sbit (s f : Nat) : Bool := Nat.beq fld(s, f, nat_lit 1) (nat_lit 1)

@[expose] noncomputable def spt (w m : Nat) (VP : Nat → Nat) (o s k q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun f ih q => strictN (nIf(sbit s f, pg w m (VP (Nat.add o f)) q, q)) ih) k q

@[expose] noncomputable def vChkS (T : Nat → Nat) (sh lm rb rm n w m pm : Nat) (Z Zi : Nat → Nat)
    (VP VC : Nat → Nat) (h hi p o i : Nat) : Bool :=
  strictB (rperm T sh lm rb rm pm i) (fun u =>
    allN p (fun e => bAnd(eq3 n w m (VP (Nat.add o e)) (Z e) u (Zi e),
      strictB (VC (Nat.add o e)) (fun s =>
        allN n (fun q => Nat.beq (pg w m h (pg w m (VP (Nat.add o e)) (pg w m hi q)))
          (spt w m VP o s p q))))))

@[expose] noncomputable def vRangeS (T : Nat → Nat) (sh lm rb rm n w m pm : Nat) (Z Zi : Nat → Nat)
    (VP VC : Nat → Nat) (h hi p st lo cnt : Nat) : Bool :=
  allN cnt (fun t =>
    vChkS T sh lm rb rm n w m pm Z Zi VP VC h hi p (Nat.mul p (Nat.add st t)) (Nat.add lo t))

end CFSG.KC.Enum

end
