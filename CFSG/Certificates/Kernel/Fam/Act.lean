module

public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CFSG.KC.Fam

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def tget (T : Nat → Nat) (sh rb i : Nat) : Nat :=
  strictN (Nat.shiftRight i sh) (fun j =>
    bitsN (T j) (Nat.mul rb (Nat.land i (Nat.sub (Nat.shiftLeft (nat_lit 1) sh) (nat_lit 1)))) rb)

@[expose] noncomputable def zeroF (_ : Nat) : Nat := nat_lit 0

@[expose] noncomputable def actRange (V P : Nat → Nat) (vm : Nat → Nat → Nat) (vldV : Nat → Bool) (M n lo m : Nat) :
    Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (vldV (V i)) (andB (Nat.blt (P i) n) (Nat.beq (vm (V i) M) (V (P i)))))
      (Nat.add lo t))) m)

@[expose] noncomputable def tposeOK (vld : Nat → Bool) (w S d A AT : Nat) : Bool :=
  andB (vld A) (andB (vld AT) (allBelow (Nat.mul d d) (Nat.add (Nat.shiftRight (Nat.mul d d) (nat_lit 6)) (nat_lit 1))
    (fun k => (fun i j => Nat.beq (bitsN A (Nat.add (Nat.mul S i) (Nat.mul w j)) w)
        (bitsN AT (Nat.add (Nat.mul S j) (Nat.mul w i)) w))
      (Nat.div k d) (Nat.mod k d))))

@[expose] noncomputable def tpose3OK (vld : Nat → Bool) (d N A AT : Nat) : Bool :=
  andB (vld A) (andB (vld AT) (allBelow (Nat.mul d d) (Nat.add (Nat.shiftRight (Nat.mul d d) (nat_lit 6)) (nat_lit 1))
    (fun k => (fun i j => andB
        (Nat.beq (bitsN A (Nat.add (Nat.mul d i) j) (nat_lit 1)) (bitsN AT (Nat.add (Nat.mul d j) i) (nat_lit 1)))
        (Nat.beq (bitsN A (Nat.add N (Nat.add (Nat.mul d i) j)) (nat_lit 1))
          (bitsN AT (Nat.add N (Nat.add (Nat.mul d j) i)) (nat_lit 1))))
      (Nat.div k d) (Nat.mod k d))))

@[expose] noncomputable def sortRange (V σ τ : Nat → Nat) (n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun k => andB (Nat.blt (σ k) n) (andB (Nat.beq (τ (σ k)) k)
        (bIf(Nat.blt (Nat.succ k) n, Nat.blt (V (σ k)) (V (σ (Nat.succ k))), true))))
      (Nat.add lo t))) m)

@[expose] noncomputable def selMat (V : Nat → Nat) (vldV : Nat → Bool) (S d BL bw n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => (fun b => nIf(andB (Nat.blt b n) (vldV (V b)), Nat.lor acc (Nat.shiftLeft (V b) (Nat.mul S k)), nat_lit 0))
      (bitsN BL (Nat.mul bw k) bw)) d

@[expose] noncomputable def selBasis (V : Nat → Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (S d BL bw n ONE Ri : Nat) : Bool :=
  andB (vld Ri) (Nat.beq (mul (selMat V vldV S d BL bw n) Ri) ONE)

@[expose] noncomputable def kdiag (d i : Nat) : Nat :=
  Nat.sub (Nat.mul i d) (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2))

@[expose] noncomputable def diagForm (w d l : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (bitsN l (Nat.mul w i) (nat_lit 1)) (kdiag d i))) d

@[expose] noncomputable def formsRange (T L : Nat → Nat) (vldV : Nat → Bool) (w d n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (vldV (L i)) (Nat.beq (Nat.xor (T i) (T (nat_lit 0))) (diagForm w d (L i))))
      (Nat.add lo t))) m)

@[expose] noncomputable def addV (p w T LV HV a b : Nat) : Nat := redP w LV HV p T (Nat.add a b)

@[expose] noncomputable def affRange (L P : Nat → Nat) (vm add : Nat → Nat → Nat) (vldV : Nat → Bool)
    (R c n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (vldV (L i)) (andB (Nat.blt (P i) n) (Nat.beq (add (vm (L i) R) c) (L (P i)))))
      (Nat.add lo t))) m)

@[expose] noncomputable def laneMagic (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.sub w (nat_lit 1)) k))) w

@[expose] noncomputable def lanePack (w n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight (Nat.mul (bitsN x (Nat.mul (Nat.mul w w) c) (Nat.mul w w)) (laneMagic w))
        (Nat.mul (Nat.sub w (nat_lit 1)) (Nat.sub w (nat_lit 1)))) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))
      (Nat.mul w c)))
    (Nat.div (Nat.add n (Nat.sub w (nat_lit 1))) w)

@[expose] noncomputable def laneLow (w n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w n)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def bitMat (w S d C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (lanePack w d (Nat.land (bitsN C (Nat.mul S i) (Nat.mul w d)) (laneLow w d))) (Nat.mul d i))) d

@[expose] noncomputable def quadIs (w S d C t : Nat) : Bool :=
  (fun P => Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih ((fun r c => Nat.beq (bitsN t (kdiag d i) (Nat.sub d i))
        (Nat.lor (Nat.land (Nat.shiftRight (Nat.xor r c) i)
            (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.sub d i)) (nat_lit 2)))
          (Nat.land (Nat.shiftRight r i) (nat_lit 1))))
      (bitsN P (Nat.mul d i) d) (lanePack d d (Nat.land (Nat.shiftRight P i) (laneLow d d))))) d)
  (bitMat w S d C)

@[expose] noncomputable def laneHigh (w n : Nat) : Nat :=
  Nat.sub (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w n)) (nat_lit 1))
    (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w n)) (nat_lit 1))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))

@[expose] noncomputable def formMat (vld : Nat → Bool) (w S d t U : Nat) : Bool :=
  andB (vld U) (Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih ((fun Ui => andB (Nat.beq (Nat.land Ui (laneHigh w d)) (nat_lit 0))
        (Nat.beq (lanePack w d Ui) (Nat.shiftLeft (bitsN t (kdiag d i) (Nat.sub d i)) i)))
      (bitsN U (Nat.mul S i) (Nat.mul w d)))) d)

@[expose] noncomputable def formRange (QF UM : Nat → Nat) (vld : Nat → Bool) (w S d n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => formMat vld w S d (QF i) (UM i)) (Nat.add lo t))) m)

@[expose] noncomputable def quadRange (QF UM P : Nat → Nat) (mul : Nat → Nat → Nat) (w S d R RT n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (Nat.blt (P i) n) (quadIs w S d (mul RT (mul (UM i) R)) (QF (P i))))
      (Nat.add lo t))) m)

@[expose] noncomputable def pullOK (mul : Nat → Nat → Nat) (vld : Nat → Bool) (w S d R RT U ts : Nat) : Bool :=
  andB (tposeOK vld w S d R RT) (quadIs w S d (mul RT (mul U R)) ts)

@[expose] noncomputable def congRange (PM P : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool) (L R n lo m : Nat) :
    Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (vld (PM i)) (andB (Nat.blt (P i) n) (Nat.beq (mul (mul L (PM i)) R) (PM (P i)))))
      (Nat.add lo t))) m)

@[expose] noncomputable def qactRange (R Q : Nat → Nat) (vm add : Nat → Nat → Nat) (vldV : Nat → Bool)
    (M z n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (vldV (R i)) (andB (Nat.blt (Q i) n)
        ((fun y => orB (Nat.beq y (R (Q i))) (Nat.beq y (add (R (Q i)) z))) (vm (R i) M))))
      (Nat.add lo t))) m)

@[expose] noncomputable def canonRange (R : Nat → Nat) (add : Nat → Nat → Nat) (z n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => Nat.blt (R i) (add (R i) z)) (Nat.add lo t))) m)

@[expose] noncomputable def projRange (R P : Nat → Nat) (vm add : Nat → Nat → Nat) (vldV : Nat → Bool)
    (M n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (vldV (R i)) (andB (Nat.blt (P i) n)
        ((fun y => (fun r => orB (Nat.beq y r) (Nat.beq y (add r r))) (R (P i))) (vm (R i) M))))
      (Nat.add lo t))) m)

@[expose] noncomputable def projCanon (R : Nat → Nat) (add : Nat → Nat → Nat) (n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => Nat.blt (R i) (add (R i) (R i))) (Nat.add lo t))) m)

@[expose] noncomputable def gramTree (w S Gm EL m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t ih => andB ih
    ((fun b => andB (Nat.ble b t) (notB (Nat.beq (bitsN Gm (Nat.add (Nat.mul S (Nat.succ t)) (Nat.mul w b)) w)
        (nat_lit 0)))) (bitsN EL (Nat.mul (nat_lit 8) t) (nat_lit 8)))) m

@[expose] noncomputable def avoidRange (V : Nat → Nat) (x lo m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t ih => andB ih (notB (Nat.beq (V (Nat.add lo t)) x))) m

@[expose] noncomputable def orbPt (LB PA : Nat → Nat) (SG : Nat → Nat → Nat) (RP rw k r i : Nat) : Bool :=
  (fun c pa => (fun rho => andB (Nat.blt c r) (andB (Nat.ble rho i)
      (andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (Nat.beq (LB (SG g i)) c)) k)
        (bIf(Nat.beq i rho, Nat.beq (Nat.shiftRight pa (nat_lit 28)) (nat_lit 0),
          (fun par g' => andB (Nat.blt g' k) (andB (Nat.beq (SG g' par) i)
              (Nat.beq (Nat.shiftRight pa (nat_lit 28)) (Nat.succ (Nat.shiftRight (PA par) (nat_lit 28))))))
            (bitsN pa (nat_lit 0) (nat_lit 24)) (bitsN pa (nat_lit 24) (nat_lit 4)))))))
    (bitsN RP (Nat.mul rw c) rw))
  (LB i) (PA i)

@[expose] noncomputable def orbRange (LB PA : Nat → Nat) (SG : Nat → Nat → Nat) (RP rw k r n lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih (orbPt LB PA SG RP rw k r (Nat.add lo t))) m)

@[expose] noncomputable def repsOK (LB : Nat → Nat) (RP rw r n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c ih => andB ih ((fun rho => andB (Nat.blt rho n) (Nat.beq (LB rho) c)) (bitsN RP (Nat.mul rw c) rw))) r

@[expose] noncomputable def cntRange (LB : Nat → Nat) (lo m S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S
    (fun t acc => strictN acc (fun a => Nat.add a (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 32) (LB (Nat.add lo t)))))) m

@[expose] noncomputable def primSubX (sizes n N E : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun mask acc => andB acc (orB (orB (orB (Nat.beq mask (nat_lit 0))
        (Nat.beq mask (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))))
        (Nat.beq (bitsN E mask (nat_lit 1)) (nat_lit 1)))
      (notB (Nat.beq (Nat.mod N (subSize sizes mask n)) (nat_lit 0)))))
    (Nat.shiftLeft (nat_lit 1) n)

@[expose] noncomputable def inB (LB : Nat → Nat) (mask i : Nat) : Bool :=
  orB (Nat.beq (LB i) (nat_lit 0)) (Nat.beq (bitsN mask (Nat.sub (LB i) (nat_lit 1)) (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def blockWit (LB G : Nat → Nat) (n mask p1 p2 : Nat) : Bool :=
  andB (Nat.blt p1 n) (andB (Nat.blt p2 n) (andB (inB LB mask p1) (andB (inB LB mask (G p1))
    (andB (inB LB mask p2) (notB (inB LB mask (G p2)))))))

@[expose] noncomputable def sizes64 (C r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft (bitsN C (Nat.mul (nat_lit 32) (Nat.succ c)) (nat_lit 32)) (Nat.mul (nat_lit 64) c)))
    (Nat.sub r (nat_lit 1))

end CFSG.KC.Fam

end
