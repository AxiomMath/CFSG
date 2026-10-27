module

public import CFSG.Certificates.Kernel.Fi22.Bound2.Lab
public import CFSG.Certificates.Kernel.Common.HOrb

public section

namespace CFSG.KC.Fi22K

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi22B.Cov CFSG.KC.HOrb CFSG.KC.LceS

@[expose] noncomputable def evalE (FS : Nat → Nat) (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) one4
    (fun q acc => strictN acc (fun x => mul4 x (FS (Nat.shiftRight (byte (wWord w) q) (nat_lit 1))))) (wLen w)

@[expose] noncomputable def omI : Nat := Nat.shiftLeft one4 (nat_lit 729)

@[expose] noncomputable def om2I : Nat := Nat.lor one4 (Nat.shiftLeft one4 (nat_lit 729))

@[expose] noncomputable def scalEq (X Y : Nat) : Bool :=
  orB (Nat.beq X Y) (orB (Nat.beq X (mul4 omI Y)) (Nat.beq X (mul4 om2I Y)))

@[expose] noncomputable def labOf (X XI p N : Nat) : Nat :=
  Nat.lor X (Nat.lor (Nat.shiftLeft XI (nat_lit 1458)) (Nat.lor (Nat.shiftLeft p (nat_lit 2916))
    (Nat.shiftLeft N (nat_lit 2917))))

@[expose] noncomputable def omK (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) om2I omI (Nat.beq k (nat_lit 1)))
    one4 (Nat.beq k (nat_lit 0))

@[expose] noncomputable def rowOK (A V r : Nat) : Bool :=
  (fun k e p N => andB (Nat.blt k (nat_lit 3))
      (andB (Nat.beq (aX V) (mul4 (omK k) (Bool.rec (motive := fun _ => Nat) A one4 (Nat.beq e (nat_lit 0)))))
        (andB (Nat.beq (aP V) p) (Nat.beq (aN V) N))))
    (Nat.land r (nat_lit 3)) (Nat.land (Nat.shiftRight r (nat_lit 2)) (nat_lit 1))
    (Nat.land (Nat.shiftRight r (nat_lit 3)) (nat_lit 1)) (Nat.shiftRight r (nat_lit 4))

@[expose] noncomputable def M256 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1)

@[expose] noncomputable def pzOf (cs : List Nat) (sh msk o : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ ih => strictN ih (fun s => Nat.add s (Nat.add
      (Nat.mul (Nat.land (Nat.shiftRight c (nat_lit 128)) M256) (Nat.land (Nat.shiftRight c sh) msk))
      (Nat.mul o (Nat.shiftRight c (nat_lit 384)))))) cs

@[expose] noncomputable def nzOf (cs : List Nat) (sh msk o : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ ih => strictN ih (fun s => Nat.add s (Nat.add
      (Nat.mul (Nat.shiftRight c (nat_lit 384)) (Nat.land (Nat.shiftRight c sh) msk))
      (Nat.mul o (Nat.land (Nat.shiftRight c (nat_lit 128)) M256))))) cs

@[expose] noncomputable def coordOK (cs : List Nat) (sh msk o md t : Nat) : Bool :=
  (fun P N => Bool.rec (motive := fun _ => Bool)
      (Nat.beq (Nat.mod (Nat.add P (Nat.mul (Nat.sub md (nat_lit 1)) N)) md) t)
      (Nat.beq P (Nat.add N t))
      (Nat.beq md (nat_lit 0)))
    (pzOf cs sh msk o) (nzOf cs sh msk o)

end CFSG.KC.Fi22K

end
