module

public import CFSG.Certificates.Kernel.Common.HOrb
public import CFSG.Certificates.Kernel.Fi22.Bound2.Rels

public section

namespace CFSG.KC.Fi22K

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.HOrb

@[expose] noncomputable def catEnt (e f : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) (Nat.add (wLen e) (wLen f)))
    (Nat.shiftLeft (Nat.lor (wWord e) (Nat.shiftLeft (wWord f) (Nat.mul (nat_lit 8) (wLen e)))) (nat_lit 12))

@[expose] noncomputable def sliceEnt (e lo cnt : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) cnt)
    (Nat.shiftLeft (Nat.land (Nat.shiftRight (wWord e) (Nat.mul (nat_lit 8) lo))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) cnt)) (nat_lit 1))) (nat_lit 12))

@[expose] noncomputable def letEnt (c : Nat) : Nat := Nat.add (nat_lit 4) (Nat.shiftLeft c (nat_lit 12))

@[expose] noncomputable def eAB (g : Nat) : Nat := subY (Nat.add (nat_lit 6) g)

@[expose] noncomputable def eHalf (g : Nat) : Nat := Nat.div (wLen (eAB g)) (nat_lit 2)

@[expose] noncomputable def sigma (g : Nat) : Nat := sliceEnt (eAB g) (Nat.succ (eHalf g)) (eHalf g)

@[expose] noncomputable def sigInv (g : Nat) : Nat := sliceEnt (eAB g) (nat_lit 0) (eHalf g)

@[expose] noncomputable def letInvAB (x : Nat) : Nat :=
  (fun g => Bool.rec (motive := fun _ => Nat) (eAB g) (invEnt (eAB g)) (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 0)))
    (Nat.succ (Nat.shiftRight x (nat_lit 1)))

@[expose] noncomputable def piInv (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc (fun a => catEnt a (letInvAB (byte (wWord w) (Nat.sub (Nat.sub (wLen w) (nat_lit 1)) k)))))
    (wLen w)

@[expose] noncomputable def pairWord (i j w : Nat) : Nat := catEnt (sigma j) (catEnt (piInv w) (sigInv i))

@[expose] noncomputable def xrelOf (i j m w : Nat) : Nat :=
  powEnt (catEnt (invEnt w) (catEnt (letEnt (Nat.mul (nat_lit 2) (Nat.sub i (nat_lit 1))))
    (catEnt w (letEnt (Nat.mul (nat_lit 2) (Nat.sub j (nat_lit 1))))))) m

@[expose] noncomputable def hWord (hl n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc (fun a => (fun x => catEnt a
        (Bool.rec (motive := fun _ => Nat) (invEnt (CFSG.KC.Fi22B.sub (Nat.shiftRight x (nat_lit 1))))
          (CFSG.KC.Fi22B.sub (Nat.shiftRight x (nat_lit 1))) (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 0))))
      (byte hl k))) n

@[expose] noncomputable def pairOK (blk : Nat → Nat) (nf UW0 UW1 XRk i j m w R1 c ρ hl hn R2 : Nat) : Bool :=
  andB (Nat.beq (xrelOf i j m w) XRk)
    (andB (walkTo blk nf (withSent (pairWord i j w)) (nat_lit 0) R1 c)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq m (Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 3) (Nat.beq ρ (nat_lit 1))))
          (andB (Nat.ble ρ (nat_lit 2))
            (walkTo blk nf (withSent (catEnt (Bool.rec (motive := fun _ => Nat) UW1 UW0 (Nat.beq ρ (nat_lit 1)))
              (hWord hl hn))) (nat_lit 0) R2 c)))
        (andB (Nat.beq c (nat_lit 0)) (Nat.beq m (nat_lit 1)))
        (Nat.beq ρ (nat_lit 0))))

end CFSG.KC.Fi22K

end
