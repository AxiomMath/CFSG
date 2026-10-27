module

public import CFSG.Certificates.Kernel.Common.HOrb

public section

namespace CFSG.KC.HSK

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

@[expose] noncomputable def hWord (sub : Nat → Nat) (hl n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc (fun a => (fun x => catEnt a
        (Bool.rec (motive := fun _ => Nat) (invEnt (sub (Nat.shiftRight x (nat_lit 1))))
          (sub (Nat.shiftRight x (nat_lit 1))) (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 0))))
      (byte hl k))) n

@[expose] def U1 : Nat := nat_lit 8196

@[expose] def U2 : Nat := nat_lit 536879116

@[expose] def U3 : Nat := nat_lit 2105352

@[expose] def U4 : Nat := nat_lit 592601706350638014496

@[expose] noncomputable def rootExp (ρ : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 6) (Nat.beq ρ (nat_lit 3)))
      (nat_lit 3) (Nat.beq ρ (nat_lit 2)))
    (nat_lit 5) (Nat.beq ρ (nat_lit 1))

@[expose] noncomputable def rootWord (ρ : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) U4 U3 (Nat.beq ρ (nat_lit 3)))
      U2 (Nat.beq ρ (nat_lit 2)))
    U1 (Nat.beq ρ (nat_lit 1))

@[expose] noncomputable def conjOK (e : Nat) : Bool :=
  (fun h => andB (Nat.beq (wLen e) (Nat.succ (Nat.mul (nat_lit 2) h)))
      (andB (Nat.beq (byte (wWord e) h) (nat_lit 0))
        (Nat.beq (sliceEnt e (nat_lit 0) h) (invEnt (sliceEnt e (Nat.succ h) h)))))
    (Nat.div (wLen e) (nat_lit 2))

@[expose] noncomputable def lettersLt (w L : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (Nat.blt (byte (wWord w) k) L)) (wLen w)

@[expose] noncomputable def pairOK (blk GW sub : Nat → Nat) (ng nf XRk i j m w R1 c ρ hl hn R2 : Nat) : Bool :=
  andB (andB (andB (Nat.ble (nat_lit 1) i) (Nat.ble i ng))
      (andB (andB (Nat.ble (nat_lit 1) j) (Nat.ble j ng)) (lettersLt w (Nat.mul (nat_lit 2) ng))))
  (andB (Nat.beq (xrelOf i j m w) XRk)
    (andB (walkTo blk nf (withSent (pairWord GW i j w)) (nat_lit 0) R1 c)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq m (rootExp ρ))
          (andB (Nat.ble ρ (nat_lit 4))
            (walkTo blk nf (withSent (catEnt (rootWord ρ) (hWord sub hl hn))) (nat_lit 0) R2 c)))
        (andB (Nat.beq c (nat_lit 0)) (Nat.beq m (nat_lit 1)))
        (Nat.beq ρ (nat_lit 0)))))

end CFSG.KC.HSK

end
