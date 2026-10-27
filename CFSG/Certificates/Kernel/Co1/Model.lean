module

public import CFSG.Certificates.Kernel.Common.DceS
public import CFSG.Certificates.Kernel.Common.Bind

public section

namespace CFSG.KC.Co1M

open CFSG.KC CFSG.KC.DceS CFSG.KC.Bind

@[expose] noncomputable def evalLce (MPT : Nat → Nat) (MM E : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idP (fun q acc =>
    (fun l => (fun x => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (pmul acc (Bool.rec (motive := fun _ => Nat) (MPT x) (pinv (MPT x)) (Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 1))))
        (andB (Nat.blt (nat_lit 0) acc) (Nat.blt x (nat_lit 255))))
      (mget MM (Nat.shiftRight l (nat_lit 1))))
    (wLet (CFSG.KC.LceS.wWord E) q)) (CFSG.KC.LceS.wLen E)

@[expose] noncomputable def relsOK (MPT RT : Nat → Nat) (MM R : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r acc => andB acc (Nat.beq (evalLce MPT MM (RT r)) idP)) R

@[expose] noncomputable def mpOK (MPT : Nat → Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc (isPerm (MPT k))) n

@[expose] noncomputable def d1LetOK (LT MPT : Nat → Nat) (NL TL MMD : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c acc => andB acc (orB (Nat.beq c TL)
    (andB (Nat.blt (mget MMD c) (nat_lit 255)) (Nat.beq (Nat.land (LT c) m64) (MPT (mget MMD c)))))) NL

@[expose] noncomputable def tFixOK (MPT ST PBT OMT : Nat → Nat) (MM K NB I0 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc
    (letB (evalLce MPT MM (ST j)) (fun g => andB (Nat.blt (nat_lit 0) g)
      (andB (Nat.beq (pmul g g) idP) (gOmOK NB (PBT I0) g (OMT I0)))))) K

@[expose] noncomputable def tGens (MPT ST : Nat → Nat) (MM K : Nat) : Nat :=
  packGens (fun j => evalLce MPT MM (ST j)) K

@[expose] noncomputable def omClosOK (LT PBT OMT OHT : Nat → Nat) (NL TL NB NO j : Nat) : Bool :=
  letB (OHT j) (fun H => Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc
    (andB (Nat.blt (hget H k) NO)
      (gOmOK NB (PBT j) (Nat.land (LT (Bool.rec (motive := fun _ => Nat) (Nat.succ k) k (Nat.blt k TL))) m64)
        (OMT (hget H k))))) (Nat.sub NL (nat_lit 1)))

@[expose] noncomputable def centOK (DRT ST : Nat → Nat) (MD TL K CH : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc
    ((fun E R => andB (Nat.beq (Nat.land R (nat_lit 255)) (Nat.add (Nat.mul (nat_lit 2) (CFSG.KC.LceS.wLen E)) (nat_lit 2)))
      (andB (Nat.rec (motive := fun _ => Bool) true (fun q acc2 => andB acc2
          (Nat.blt (mget MD (Nat.shiftRight (wLet (CFSG.KC.LceS.wWord E) q) (nat_lit 1))) (nat_lit 255))) (CFSG.KC.LceS.wLen E))
        ((fun s n => isRot (Nat.shiftRight R (nat_lit 8)) (Nat.add (Nat.mul (nat_lit 2) n) (nat_lit 2))
            (Nat.lor TL (Nat.lor (Nat.shiftLeft s (nat_lit 8)) (Nat.lor (Nat.shiftLeft TL (Nat.mul (nat_lit 8) (Nat.succ n)))
              (Nat.shiftLeft s (Nat.mul (nat_lit 8) (Nat.add n (nat_lit 2))))))))
          (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q acc3 => Nat.lor acc3 (Nat.shiftLeft
            (mget MD (Nat.shiftRight (wLet (CFSG.KC.LceS.wWord E) q) (nat_lit 1))) (Nat.mul (nat_lit 8) q))) (CFSG.KC.LceS.wLen E))
          (CFSG.KC.LceS.wLen E))))
      (ST j) (DRT (hget CH j)))) K

end CFSG.KC.Co1M

end
