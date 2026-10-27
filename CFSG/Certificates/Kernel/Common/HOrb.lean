module

public import CFSG.Certificates.Kernel.Common.LceS

public section

namespace CFSG.KC.HOrb

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def dep (DT : Nat → Nat) (y : Nat) : Nat :=
  Nat.land (Nat.shiftRight (DT (Nat.shiftRight y (nat_lit 10)))
    (Nat.mul (nat_lit 4) (Nat.land y (nat_lit 1023)))) (nat_lit 15)

@[expose] noncomputable def isRoot (RO nr y : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k acc => orB acc (Nat.beq (Nat.land (Nat.shiftRight RO (Nat.mul (nat_lit 20) k)) (nat_lit 1048575)) y)) nr

@[expose] noncomputable def hwalk (blk : Nat → Nat) (nf : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ st => st)
    (fun _ ih R st => strictN (refStep blk nf (Nat.land R (nat_lit 4294967295)) st)
      (ih (Nat.shiftRight R (nat_lit 32)))) k

@[expose] noncomputable def walkTo (blk : Nat → Nat) (nf w x R y : Nat) : Bool :=
  Nat.beq (hwalk blk nf (wLen w) R (wStart x (wWord w))) (Nat.add y (nat_lit 1048576))

@[expose] noncomputable def orbStep (blk DT SW LVs : Nat → Nat) (nf nSW RO nr y S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat) S
      (strictN (dep DT y) (fun d =>
        Bool.rec (motive := fun _ => Nat)
          (strictN (Nat.land S (nat_lit 1048575)) (fun x =>
            strictN (Nat.land (Nat.shiftRight S (nat_lit 20)) (nat_lit 255)) (fun j =>
              strictN (SW j) (fun w =>
                Bool.rec (motive := fun _ => Nat) (nat_lit 0)
                  (Nat.shiftRight S (Nat.add (nat_lit 28) (Nat.mul (nat_lit 32) (wLen w))))
                  (andB (Nat.blt j nSW) (andB (alive LVs x)
                    (andB (Nat.beq (Nat.succ (dep DT x)) d)
                      (walkTo blk nf w x (Nat.shiftRight S (nat_lit 28)) y))))))))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S (isRoot RO nr y))
          (Nat.beq d (nat_lit 0))))
      (alive LVs y))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def orbChunk (blk DT SW LVs : Nat → Nat) (nf nSW RO nr C Y : Nat) : Nat :=
  strictN (Nat.land C (nat_lit 1048575)) (fun y0 =>
    strictN (Nat.land (Nat.shiftRight C (nat_lit 20)) (nat_lit 511)) (fun cnt =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.add (Nat.add y0 cnt) (nat_lit 1))
          (Nat.beq (Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
              (fun k ih S => strictN (orbStep blk DT SW LVs nf nSW RO nr
                (Nat.add y0 (Nat.sub (Nat.sub cnt (nat_lit 1)) k)) S) ih)
              cnt (Nat.shiftRight C (nat_lit 29))) (nat_lit 1)))
        (Nat.beq Y (Nat.succ y0))))

@[expose] noncomputable def runOrb (blk DT SW LVs : Nat → Nat) (nf nSW RO nr : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun Y => Y)
    (fun C _ ih Y => strictN (orbChunk blk DT SW LVs nf nSW RO nr C Y) ih) Cs

@[expose] noncomputable def rootOK (blk DT : Nat → Nat) (nf RO k w R : Nat) : Bool :=
  letB (Nat.land (Nat.shiftRight RO (Nat.mul (nat_lit 20) k)) (nat_lit 1048575)) (fun r =>
    andB (walkTo blk nf w (nat_lit 0) R r) (Nat.beq (dep DT r) (nat_lit 0)))

@[expose] noncomputable def byte (W i : Nat) : Nat :=
  Nat.land (Nat.shiftRight W (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def invW (W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (Nat.xor (byte W (Nat.sub (Nat.sub n (nat_lit 1)) k)) (nat_lit 1))
      (Nat.mul (nat_lit 8) k))) n

@[expose] noncomputable def withSent (e : Nat) : Nat :=
  Nat.add e (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 12) (Nat.mul (nat_lit 8) (wLen e))))

@[expose] noncomputable def invEnt (e : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) (wLen e)) (Nat.shiftLeft (invW (wWord e) (wLen e)) (nat_lit 12))

@[expose] noncomputable def swOK (SW ST : Nat → Nat) (K : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j acc => andB acc (andB (Nat.beq (SW (Nat.mul (nat_lit 2) j)) (withSent (ST j)))
      (Nat.beq (SW (Nat.succ (Nat.mul (nat_lit 2) j))) (withSent (invEnt (ST j)))))) K

@[expose] noncomputable def commEnt (e : Nat) : Nat :=
  (fun n W => Nat.add (Nat.mul (nat_lit 4) (Nat.add (Nat.mul (nat_lit 2) n) (nat_lit 2)))
    (Nat.shiftLeft
      (Nat.lor (nat_lit 1) (Nat.lor (Nat.shiftLeft (invW W n) (nat_lit 8))
        (Nat.shiftLeft W (Nat.mul (nat_lit 8) (Nat.add n (nat_lit 2))))))
      (nat_lit 12)))
  (wLen e) (wWord e)

@[expose] noncomputable def powEnt (e m : Nat) : Nat :=
  (fun n W => Nat.add (Nat.mul (nat_lit 4) (Nat.mul m n))
    (Nat.shiftLeft (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.lor acc (Nat.shiftLeft W (Nat.mul (nat_lit 8) (Nat.mul n k)))) m) (nat_lit 12)))
  (wLen e) (wWord e)

@[expose] noncomputable def commPow (e m : Nat) : Nat := powEnt (commEnt e) m

end CFSG.KC.HOrb

end
