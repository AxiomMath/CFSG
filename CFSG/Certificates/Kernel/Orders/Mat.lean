module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Ord

open CFSG.KC.Loop

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def bitsN (x o m : Nat) : Nat :=
  Nat.land (Nat.shiftRight x o) (Nat.sub (Nat.shiftLeft (nat_lit 1) m) (nat_lit 1))

@[expose] noncomputable def mulU (w S d CM RM A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.mul (Nat.land (Nat.shiftRight A (Nat.mul w k)) CM)
      (Nat.land (Nat.shiftRight B (Nat.mul S k)) RM))) d

@[expose] noncomputable def csub (w L H c x : Nat) : Nat :=
  Nat.sub x (Nat.mul (Nat.shiftRight (Nat.land (Nat.sub (Nat.lor x H) (Nat.mul c L)) H)
    (Nat.sub w (nat_lit 1))) c)

@[expose] noncomputable def redP (w L H p T x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => csub w L H (Nat.shiftLeft p (Nat.sub T i)) acc) (Nat.succ T)

@[expose] noncomputable def mulR (p w S d T L H CM RM A B : Nat) : Nat :=
  redP w L H p T (mulU w S d CM RM A B)

@[expose] noncomputable def vecU (w S d RM v M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.mul (bitsN v (Nat.mul w k) w)
      (Nat.land (Nat.shiftRight M (Nat.mul S k)) RM))) d

@[expose] noncomputable def vecR (p w S d T LV HV RM v M : Nat) : Nat :=
  redP w LV HV p T (vecU w S d RM v M)

@[expose] noncomputable def validM (p nb L H X : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight X nb) (nat_lit 0))
    (andB (Nat.beq (Nat.land X H) (nat_lit 0))
      (Nat.beq (Nat.land (Nat.sub (Nat.lor X H) (Nat.mul p L)) H) (nat_lit 0)))

@[expose] noncomputable def rowsOf (S r0 h M : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.mul S r0)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul S h)) (nat_lit 1))

@[expose] noncomputable def rowsMulU (w S g m CMh RM X B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun a => strictN (rowsOf S (Nat.mul g j) g B) (fun Bg =>
        Nat.rec (motive := fun _ => Nat) a
          (fun i acc2 => Nat.add acc2 (Nat.mul
            (Nat.land (Nat.shiftRight X (Nat.mul w (Nat.add (Nat.mul g j) i))) CMh)
            (Nat.land (Nat.shiftRight Bg (Nat.mul S i)) RM))) g))) m

@[expose] noncomputable def rowsMulR (p w S g m T Lh Hh CMh RM X B : Nat) : Nat :=
  redP w Lh Hh p T (rowsMulU w S g m CMh RM X B)

@[expose] noncomputable def tbl (w S g RM B b v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.add acc (Nat.mul (bitsN v (Nat.mul w t) w)
      (Nat.land (Nat.shiftRight (rowsOf S (Nat.mul g b) g B) (Nat.mul S t)) RM))) g

@[expose] noncomputable def rowMulU (w S g m RM B x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.add acc (strictN (bitsN x (Nat.mul (Nat.mul w g) b) (Nat.mul w g))
      (fun v => tbl w S g RM B b v))) m

@[expose] noncomputable def mulTree (p w S g m T LV HV RM B : Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih X n => Bool.rec (motive := fun _ => Nat)
      ((fun n1 => Nat.lor (ih (rowsOf S (nat_lit 0) n1 X) n1)
          (Nat.shiftLeft (ih (Nat.shiftRight X (Nat.mul S n1)) (Nat.sub n n1)) (Nat.mul S n1)))
        (Nat.div n (nat_lit 2)))
      (redP w LV HV p T (rowMulU w S g m RM B X))
      (Nat.beq n (nat_lit 1))) f

@[expose] noncomputable def mulG (p w S d g m T f LV HV RM A B : Nat) : Nat :=
  mulTree p w S g m T LV HV RM B f A d

@[expose] noncomputable def rep1 (s n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul s n)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) s) (nat_lit 1))

@[expose] noncomputable def constsOK (p w S d T L H CM RM ONE LV HV : Nat) : Bool :=
  andB (Nat.ble (nat_lit 2) p)
  (andB (Nat.beq S (Nat.mul d w))
  (andB (Nat.blt (Nat.mul d (Nat.mul (Nat.sub p (nat_lit 1)) (Nat.sub p (nat_lit 1))))
    (Nat.shiftLeft (nat_lit 1) (Nat.sub w (nat_lit 1))))
  (andB (Nat.ble (Nat.shiftLeft p T) (Nat.shiftLeft (nat_lit 1) (Nat.sub w (nat_lit 1))))
  (andB (Nat.ble (Nat.shiftLeft (nat_lit 1) (Nat.sub w (nat_lit 1))) (Nat.shiftLeft p (Nat.succ T)))
  (andB (Nat.beq L (rep1 w (Nat.mul d d)))
  (andB (Nat.beq H (Nat.shiftLeft L (Nat.sub w (nat_lit 1))))
  (andB (Nat.beq CM (Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)) (rep1 S d)))
  (andB (Nat.beq RM (Nat.sub (Nat.shiftLeft (nat_lit 1) S) (nat_lit 1)))
  (andB (Nat.beq ONE (rep1 (Nat.add S w) d))
  (andB (Nat.beq LV (rep1 w d))
    (Nat.beq HV (Nat.shiftLeft LV (Nat.sub w (nat_lit 1))))))))))))))

end CFSG.KC.Ord

end
