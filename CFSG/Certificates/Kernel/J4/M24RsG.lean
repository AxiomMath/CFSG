module

public import CFSG.Certificates.Kernel.J4.M24Rs

public section

namespace CFSG.KM24

@[expose] noncomputable def substFits (L : List Nat) (g ns : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun h _ ih => mAnd (Prod.rec (motive := fun _ => Bool)
        (fun c _ => Nat.blt (Nat.add (pn h) (Nat.mul c ns)) (nat_lit 65536)) (occ (pw h) (pn h) g))
      ih) L

@[expose] noncomputable def stepFits (r : Nat) (L : List Nat) : Bool :=
  Bool.rec
    (Bool.rec true
      (Nat.blt (Nat.add (pn (getR L (fld r (nat_lit 18)))) (pn (getR L (fld r (nat_lit 2)))))
        (nat_lit 65536))
      (Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 1)))
    (substFits L (fld r (nat_lit 2)) (pn (getR L (fld r (nat_lit 18)))))
    (Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 0))

@[expose] noncomputable def stepG (r : Nat) (s : Bool × (List Nat × Nat)) : Bool × (List Nat × Nat) :=
  Prod.rec (motive := fun _ => Bool × (List Nat × Nat)) (fun ok LG =>
    Prod.rec (motive := fun _ => Bool × (List Nat × Nat)) (fun L G =>
      Bool.rec (Prod.mk false (Prod.mk L G)) (step r (Prod.mk ok (Prod.mk L G))) (stepFits r L)) LG) s

@[expose] noncomputable def replayG (B m : Nat) (s : Bool × (List Nat × Nat)) : Bool × (List Nat × Nat) :=
  Nat.rec (motive := fun _ => Bool × (List Nat × Nat)) s
    (fun k acc => stepG (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 72) k))
      (nat_lit 4722366482869645213695)) acc) m

@[expose] noncomputable def chkReplayG (Bk m : Nat) (A B : List Nat) (GA GB : Nat) : Bool :=
  mAnd (Nat.blt Bk (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 72) m)))
    (Prod.rec (motive := fun _ => Bool) (fun ok LG =>
      Prod.rec (motive := fun _ => Bool) (fun L G => mAnd ok (mAnd (eqRL L B) (Nat.beq G GB))) LG)
      (replayG Bk m (Prod.mk true (Prod.mk A GA))))

@[expose] noncomputable def rtBind (RT : Nat → Nat) (Rn : List Nat) (nR k2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => mAnd (chkByteRel Rn r (Nat.land (Nat.shiftRight (RT r) (nat_lit 2)) (nat_lit 1023)) k2
      (Nat.shiftRight (RT r) (nat_lit 12))) ih) nR

@[expose] noncomputable def allLet (W n c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => mAnd (Nat.beq (Nat.land (Nat.shiftRight W (Nat.mul (nat_lit 8) i)) (nat_lit 255)) c) ih) n

end CFSG.KM24

end
