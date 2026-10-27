module

public import CFSG.Certificates.Kernel.Common.HOrb
public import CFSG.Certificates.Kernel.Co2.Bound.Rels

public section

namespace CFSG.KC.Co2K

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.HOrb

@[expose] noncomputable def catEnt (e f : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) (Nat.add (wLen e) (wLen f)))
    (Nat.shiftLeft (Nat.lor (wWord e) (Nat.shiftLeft (wWord f) (Nat.mul (nat_lit 8) (wLen e)))) (nat_lit 12))

@[expose] noncomputable def sliceEnt (e lo cnt : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) cnt)
    (Nat.shiftLeft (Nat.land (Nat.shiftRight (wWord e) (Nat.mul (nat_lit 8) lo))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) cnt)) (nat_lit 1))) (nat_lit 12))

@[expose] noncomputable def letEnt (c : Nat) : Nat := Nat.add (nat_lit 4) (Nat.shiftLeft c (nat_lit 12))

@[expose] noncomputable def gHalf (GW : Nat → Nat) (g : Nat) : Nat := Nat.div (wLen (GW g)) (nat_lit 2)

@[expose] noncomputable def sigma (GW : Nat → Nat) (g : Nat) : Nat :=
  sliceEnt (GW g) (Nat.succ (gHalf GW g)) (gHalf GW g)

@[expose] noncomputable def sigInv (GW : Nat → Nat) (g : Nat) : Nat := sliceEnt (GW g) (nat_lit 0) (gHalf GW g)

@[expose] noncomputable def letInvAB (GW : Nat → Nat) (x : Nat) : Nat :=
  (fun g => Bool.rec (motive := fun _ => Nat) (GW g) (invEnt (GW g)) (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 0)))
    (Nat.succ (Nat.shiftRight x (nat_lit 1)))

@[expose] noncomputable def piInv (GW : Nat → Nat) (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc (fun a => catEnt a (letInvAB GW (byte (wWord w) (Nat.sub (Nat.sub (wLen w) (nat_lit 1)) k)))))
    (wLen w)

@[expose] noncomputable def pairWord (GW : Nat → Nat) (i j w : Nat) : Nat :=
  catEnt (sigma GW j) (catEnt (piInv GW w) (sigInv GW i))

@[expose] noncomputable def xrelOf (i j m w : Nat) : Nat :=
  powEnt (catEnt (invEnt w) (catEnt (letEnt (Nat.mul (nat_lit 2) (Nat.sub i (nat_lit 1))))
    (catEnt w (letEnt (Nat.mul (nat_lit 2) (Nat.sub j (nat_lit 1))))))) m

@[expose] noncomputable def hWord (hl n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc (fun a => (fun x => catEnt a
        (Bool.rec (motive := fun _ => Nat) (invEnt (CFSG.KC.Co2B.sub (Nat.shiftRight x (nat_lit 1))))
          (CFSG.KC.Co2B.sub (Nat.shiftRight x (nat_lit 1))) (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 0))))
      (byte hl k))) n

@[expose] noncomputable def rootExp (ρ : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 3) (Nat.beq ρ (nat_lit 2)))
    (nat_lit 4) (Nat.beq ρ (nat_lit 1))

@[expose] noncomputable def rootWord (U1 U2 U3 U4 ρ : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) U4 U3 (Nat.beq ρ (nat_lit 3)))
      U2 (Nat.beq ρ (nat_lit 2)))
    U1 (Nat.beq ρ (nat_lit 1))

@[expose] noncomputable def pairOK (blk GW : Nat → Nat) (nf U1 U2 U3 U4 XRk i j m w R1 c ρ hl hn R2 : Nat) : Bool :=
  andB (Nat.beq (xrelOf i j m w) XRk)
    (andB (walkTo blk nf (withSent (pairWord GW i j w)) (nat_lit 0) R1 c)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq m (rootExp ρ))
          (andB (Nat.ble ρ (nat_lit 4))
            (walkTo blk nf (withSent (catEnt (rootWord U1 U2 U3 U4 ρ) (hWord hl hn))) (nat_lit 0) R2 c)))
        (andB (Nat.beq c (nat_lit 0)) (Nat.beq m (nat_lit 1)))
        (Nat.beq ρ (nat_lit 0))))

end CFSG.KC.Co2K

end
