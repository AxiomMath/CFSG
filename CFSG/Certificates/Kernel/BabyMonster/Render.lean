module

public import CFSG.Certificates.Kernel.BabyMonster.F2

public section

namespace CFSG.KC.BM

@[expose] noncomputable def rep (x p c : Nat) : Nat :=
  Nat.mul x (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul p c)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) p) (nat_lit 1)))

@[expose] noncomputable def onesN (k : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1)

@[expose] noncomputable def spK (g : Nat) : Nat := rep (onesN g) (Nat.mul (nat_lit 16) g) (Nat.div (nat_lit 4096) g)

@[expose] noncomputable def spKs : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun L acc => List.cons (spK (Nat.shiftLeft (nat_lit 1) L)) acc) (nat_lit 13)

@[expose] noncomputable def spread8 (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun K _ ih g x => forceB
      (Nat.lor (Nat.land x K) (Nat.shiftLeft (Nat.land x (Nat.shiftLeft K g)) (Nat.mul (nat_lit 7) g)))
      (fun x' => ih (Nat.shiftRight g (nat_lit 1)) x'))
    spKs (nat_lit 4096) r

@[expose] noncomputable def nlM (u : Nat) : Nat :=
  Nat.land (rep (Nat.shiftLeft (onesN (Nat.mul (nat_lit 640) u)) (Nat.mul (nat_lit 640) u))
      (Nat.mul (nat_lit 1296) u) (Nat.add (Nat.div (nat_lit 4425) (Nat.mul (nat_lit 162) u)) (nat_lit 1)))
    (onesN (nat_lit 35400))

@[expose] noncomputable def nlMs : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun t acc => List.cons (nlM (Nat.shiftLeft (nat_lit 1) t)) acc) (nat_lit 6)

@[expose] noncomputable def nlIns (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun M _ ih u x => forceB
      (Nat.lor (Nat.sub x (Nat.land x M)) (Nat.shiftLeft (Nat.land x M) (Nat.mul (nat_lit 8) u)))
      (fun x' => ih (Nat.shiftRight u (nat_lit 1)) x'))
    nlMs (nat_lit 32) x

@[expose] noncomputable def digit0 : Nat := rep (nat_lit 48) (nat_lit 8) (nat_lit 4370)

@[expose] noncomputable def newlines : Nat :=
  Nat.lor (rep (Nat.shiftLeft (nat_lit 10) (nat_lit 640)) (nat_lit 648) (nat_lit 54))
    (Nat.shiftLeft (nat_lit 10) (nat_lit 35392))

@[expose] noncomputable def renderRow (r : Nat) : Nat :=
  Nat.lor (nlIns (Nat.lor (spread8 r) digit0)) newlines

@[expose] noncomputable def blockText (blk : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih sh acc => forceB (Nat.lor acc (Nat.shiftLeft (renderRow r) sh))
      (fun acc' => ih (Nat.add sh (nat_lit 35400)) acc'))
    blk (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def textOK (blk : List Nat) (P : Nat) : Bool := Nat.beq (blockText blk) P

@[expose] noncomputable def hdrOK (h : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight h (nat_lit 160)) (nat_lit 10))
    (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih (notB (Nat.beq (Nat.land (Nat.shiftRight h (Nat.mul (nat_lit 8) k)) (nat_lit 255))
        (nat_lit 10)))) (nat_lit 20))

end CFSG.KC.BM

end
