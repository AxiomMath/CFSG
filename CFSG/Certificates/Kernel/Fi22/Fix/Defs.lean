module

public import CFSG.Certificates.Kernel.Common.HOrb
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Fi22F

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.HOrb

@[expose] def nP : Nat := nat_lit 3510

@[expose] noncomputable def pf (Q i : Nat) : Nat :=
  Nat.land (Nat.shiftRight Q (Nat.mul (nat_lit 12) i)) (nat_lit 4095)

@[expose] noncomputable def lv (LV i : Nat) : Nat :=
  Nat.land (Nat.shiftRight LV (Nat.mul (nat_lit 16) i)) (nat_lit 65535)

@[expose] noncomputable def ref (Rs i : Nat) : Nat :=
  Nat.land (Nat.shiftRight Rs (Nat.mul (nat_lit 32) i)) (nat_lit 4294967295)

@[expose] noncomputable def letW (c : Nat) : Nat :=
  withSent (Nat.add (nat_lit 4) (Nat.shiftLeft c (nat_lit 12)))

@[expose] noncomputable def letOK (blk : Nat → Nat) (nf LV L Rs c : Nat) : Bool :=
  allBelow nP (nat_lit 55) (fun i => walkTo blk nf (letW c) (lv LV i) (ref Rs i) (lv LV (pf L i)))

@[expose] noncomputable def rangeOK (R : Nat) : Bool :=
  allBelow nP (nat_lit 55) (fun i => Nat.blt (pf R i) nP)

@[expose] noncomputable def idOK (Q : Nat) : Bool :=
  allBelow nP (nat_lit 55) (fun i => Nat.beq (pf Q i) i)

@[expose] noncomputable def compOK (Q R Q' : Nat) : Bool :=
  allBelow nP (nat_lit 55) (fun i => Nat.beq (pf Q' i) (pf R (pf Q i)))

@[expose] noncomputable def compMap (Q R : Nat) : Nat :=
  sumBelow nP (nat_lit 55) (fun i => Nat.shiftLeft (pf R (pf Q i)) (Nat.mul (nat_lit 12) i))

@[expose] noncomputable def chainOK (Qs base : Nat → Nat) (k0 cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB ih (compOK (Qs (Nat.add k0 k)) (base (Nat.add k0 k)) (Qs (Nat.succ (Nat.add k0 k)))))
    cnt

end CFSG.KC.Fi22F

end
