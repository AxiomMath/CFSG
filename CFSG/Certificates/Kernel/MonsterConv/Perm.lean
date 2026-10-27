module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.MonsterConv.Perm

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def dsw (s m x : Nat) : Nat :=
  (fun t => Nat.xor x (Nat.xor t (Nat.shiftLeft t s)))
    (Nat.land (Nat.xor (Nat.shiftRight x s) x) m)

@[expose] noncomputable def repU (W P : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul W P)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))

@[expose] noncomputable def ones (W : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)

@[expose] noncomputable def idPlane (W b : Nat) : Nat :=
  Nat.mul (Nat.div (ones W) (ones (Nat.shiftLeft (nat_lit 2) b)))
    (Nat.shiftLeft (ones (Nat.shiftLeft (nat_lit 1) b)) (Nat.shiftLeft (nat_lit 1) b))

@[expose] noncomputable def idP (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft (idPlane (Nat.shiftLeft (nat_lit 1) k) b)
      (Nat.mul b (Nat.shiftLeft (nat_lit 1) k)))) k

@[expose] noncomputable def stageShift (k i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.shiftLeft (nat_lit 1) (Nat.sub (Nat.add i (nat_lit 1)) k))
    (Nat.shiftLeft (nat_lit 1) (Nat.sub (Nat.sub k (nat_lit 1)) i))
    (Nat.blt i k)

@[expose] noncomputable def netApply (k W U N X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => strictN
      ((fun i => dsw (stageShift k i)
          (Nat.mul (Nat.land (Nat.shiftRight N (Nat.mul i W)) (ones W)) U) x)
        (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) j)) ih)
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) X

@[expose] noncomputable def netsApply (k W U : Nat) (Ns : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun N _ ih x => strictN (netApply k W U N x) ih) Ns X

@[expose] noncomputable def rawPlane (RAW rec n h c b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (Nat.land (Nat.shiftRight RAW (Nat.add (Nat.mul (nat_lit 32) c) b))
      (Nat.div (ones (Nat.mul rec n)) (ones rec)))
    (fun j x =>
      (fun g => (fun lo => Nat.lor (Nat.land x lo)
          (Nat.shiftRight (Nat.land x (Nat.shiftLeft lo (Nat.mul rec g))) (Nat.mul (Nat.sub rec (nat_lit 1)) g)))
        (Nat.mul (Nat.div (ones (Nat.mul rec (Nat.shiftLeft (nat_lit 1) h)))
            (ones (Nat.mul rec (Nat.shiftLeft g (nat_lit 1))))) (ones g)))
      (Nat.shiftLeft (nat_lit 1) j)) h

@[expose] noncomputable def colPlanes (RAW rec n k c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (Nat.lor (rawPlane RAW rec n k c b)
        (Nat.land (idPlane (Nat.shiftLeft (nat_lit 1) k) b)
          (Nat.xor (ones (Nat.shiftLeft (nat_lit 1) k)) (ones n))))
      (Nat.mul b (Nat.shiftLeft (nat_lit 1) k)))) k

@[expose] noncomputable def highOK (RAW rec n k m : Nat) : Bool :=
  andB (Nat.beq rec (Nat.mul (nat_lit 32) m))
    (andB (Nat.blt RAW (Nat.shiftLeft (nat_lit 1) (Nat.mul rec n)))
      (Nat.beq (Nat.land RAW
        (Nat.mul (Nat.div (ones (Nat.mul rec n)) (ones (nat_lit 32))) (Nat.sub (ones (nat_lit 32)) (ones k))))
        (nat_lit 0)))

@[expose] noncomputable def colOK (RAW rec n k c N : Nat) : Bool :=
  Nat.beq (netApply k (Nat.shiftLeft (nat_lit 1) k) (repU (Nat.shiftLeft (nat_lit 1) k) k) N (idP k))
    (colPlanes RAW rec n k c)

@[expose] noncomputable def wordId (k : Nat) (Ns : List Nat) : Bool :=
  Nat.beq (netsApply k (Nat.shiftLeft (nat_lit 1) k) (repU (Nat.shiftLeft (nat_lit 1) k) k) Ns (idP k))
    (idP k)

@[expose] noncomputable def wordNet (k : Nat) (Ns : List Nat) (N : Nat) : Bool :=
  Nat.beq (netsApply k (Nat.shiftLeft (nat_lit 1) k) (repU (Nat.shiftLeft (nat_lit 1) k) k) Ns (idP k))
    (netApply k (Nat.shiftLeft (nat_lit 1) k) (repU (Nat.shiftLeft (nat_lit 1) k) k) N (idP k))

@[expose] noncomputable def rawEnt (RAW rec p c : Nat) : Nat :=
  Nat.land (Nat.shiftRight RAW (Nat.add (Nat.mul rec p) (Nat.mul (nat_lit 32) c))) (ones (nat_lit 32))

@[expose] noncomputable def orbStep (k : Nat) (Ns : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) X
    (fun N _ acc => Nat.lor acc (netApply k (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1) N X)) Ns

@[expose] noncomputable def orbitOK (k : Nat) (Ns : List Nat) (r R M : Nat) : Bool :=
  andB (Nat.beq (orbStep k Ns M) M)
    (Nat.beq (Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) r)
      (fun _ X => strictN (orbStep k Ns X) (fun Y => Y)) R) M)

@[expose] noncomputable def fixedSet (k F : Nat) : Nat :=
  Nat.xor (ones (Nat.shiftLeft (nat_lit 1) k))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b acc => Nat.lor acc
        (Nat.land (Nat.xor (Nat.shiftRight F (Nat.mul b (Nat.shiftLeft (nat_lit 1) k))) (idPlane (Nat.shiftLeft (nat_lit 1) k) b))
          (ones (Nat.shiftLeft (nat_lit 1) k)))) k)

end CFSG.KC.MonsterConv.Perm

end
