module

public import CFSG.Certificates.Kernel.BabyMonster.LatCheck

public section

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.BM.Lat CFSG.KC.YModel

@[expose] noncomputable def isDig (c : Nat) : Bool :=
  andB (isB64 c) (notB (Nat.beq c (nat_lit 61)))

@[expose] noncomputable def entV (N i : Nat) : Nat :=
  (fun a b c => Bool.rec (motive := fun _ => Nat) (nat_lit 262144)
      (Nat.add (Nat.add (Nat.mul (b64v a) (nat_lit 4096)) (Nat.mul (b64v b) (nat_lit 64))) (b64v c))
      (andB (isDig a) (andB (isDig b) (isDig c))))
    (chAt N (Nat.mul (nat_lit 3) i)) (chAt N (Nat.add (Nat.mul (nat_lit 3) i) (nat_lit 1)))
    (chAt N (Nat.add (Nat.mul (nat_lit 3) i) (nat_lit 2)))

@[expose] noncomputable def lineOK (p : Nat × Nat) : Bool :=
  (fun e => andB (Nat.blt (nat_lit 0) e) (andB (Nat.beq (Nat.add (Nat.mul (nat_lit 3) e) (nat_lit 1)) p.2)
    (andB (Nat.beq (chAt p.1 (Nat.mul (nat_lit 3) e)) (nat_lit 10))
      (andB (Nat.beq (Nat.div (entV p.1 (Nat.sub e (nat_lit 1))) (nat_lit 65536)) (nat_lit 1))
        (Nat.rec (motive := fun _ => Bool) true
          (fun i ih => andB ih (Nat.blt (entV p.1 i) (nat_lit 262144))) e)))))
    (Nat.div p.2 (nat_lit 3))

@[expose] noncomputable def monoOK (p : Nat × Nat) (T : Nat) : Bool :=
  andB (Nat.beq p.2 (nat_lit 13114)) (andB (lineOK p)
    (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih ((fun v f => andB (Nat.beq (Nat.div v (nat_lit 65536)) (nat_lit 1))
          (andB (Nat.beq (Nat.mod v (nat_lit 8192)) (Nat.mod f (nat_lit 8192)))
            (Nat.beq (Nat.mod (Nat.div v (nat_lit 8192)) (nat_lit 8))
              (Nat.div f (nat_lit 8192)))))
        (entV p.1 k) (Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 16) k)) (nat_lit 65535))))
      (nat_lit 4371)))

@[expose] noncomputable def numCode (c : Nat) : Nat :=
  lget [nat_lit 8, nat_lit 2040, nat_lit 4, nat_lit 2044, nat_lit 2, nat_lit 2046] c

@[expose] noncomputable def forceP (v : Nat) (x : Nat × Nat) : Nat × Nat :=
  Bool.rec (motive := fun _ => Nat × Nat) x x (Nat.beq v (nat_lit 0))

@[expose] noncomputable def sparseRun (SG : List (List Nat)) (N i n : Nat) : Nat × Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat) (fun _ st => st)
    (fun _ ih i st => (fun v => (fun j c l =>
        (fun f => ih (Nat.succ i)
          (Bool.rec (motive := fun _ => Nat × Nat) (Nat.lor st.1 (nat_lit 8192), nat_lit 0)
            (Bool.rec (motive := fun _ => Nat × Nat) (st.1, f)
              (Bool.rec (motive := fun _ => Nat × Nat) (Nat.lor st.1 (nat_lit 8192), nat_lit 0)
                (Nat.succ st.1, nat_lit 0) (Nat.beq f (recOf SG st.1)))
              (Nat.beq l (nat_lit 1)))
            (andB (Nat.blt v (nat_lit 262144)) (andB (Nat.ble c (nat_lit 5))
              (Nat.beq (Nat.land (Nat.shiftRight st.2 (Nat.mul (nat_lit 16) j)) (nat_lit 65535))
                (nat_lit 0))))))
          (Nat.lor st.2 (Nat.shiftLeft (numCode c) (Nat.mul (nat_lit 16) j))))
        (Nat.mod v (nat_lit 8192)) (Nat.mod (Nat.div v (nat_lit 8192)) (nat_lit 8))
        (Nat.div v (nat_lit 65536)))
      (entV N i)) n i

@[expose] noncomputable def appN (L₁ L₂ : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) L₂ (fun x _ ih => List.cons x ih) L₁

@[expose] noncomputable def splitN (k : Nat) : Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun N => List.cons N List.nil)
    (fun d ih N => (fun h => appN (ih (Nat.land N (ones (Nat.mul (nat_lit 8) h))))
        (ih (Nat.shiftRight N (Nat.mul (nat_lit 8) h))))
      (Nat.mul k (Nat.shiftLeft (nat_lit 1) d)))

@[expose] noncomputable def sparseOK (p : Nat × Nat) (SG : List (List Nat)) : Bool :=
  andB (lineOK p) (andB (Nat.ble p.2 (nat_lit 786432))
    ((fun e => (fun st => andB (Nat.beq st.1 (nat_lit 4371)) (Nat.beq st.2 (nat_lit 0)))
      (List.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat) (fun _ st => st)
        (fun N _ ih m st => (fun c => (fun st' => forceP st'.1 (ih (Nat.sub m c) st'))
            (sparseRun SG N 0 c st))
          (Nat.min m (nat_lit 64)))
        (splitN (nat_lit 192) (nat_lit 12) p.1) e (nat_lit 0, nat_lit 0)))
      (Nat.div p.2 (nat_lit 3))))

@[expose] noncomputable def noNL (N m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB ih (notB (Nat.beq (chAt N k) (nat_lit 10)))) m

@[expose] noncomputable def linesAt (CH : List (Nat × Nat)) (S : List Nat) : Bool :=
  andB (Nat.beq (lget S (nat_lit 0)) (nat_lit 0))
    ((fun r => andB (Nat.beq r.1 (Nat.sub (lenL S) (nat_lit 1))) (Nat.beq r.2 (lenP CH)))
      (List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun k p => (k, p))
        (fun q _ ih k p => Bool.rec (motive := fun _ => Nat × Nat) (nat_lit 100000, nat_lit 0)
          (Bool.rec (motive := fun _ => Nat × Nat) (ih k (Nat.succ p))
            (Bool.rec (motive := fun _ => Nat × Nat) (nat_lit 100000, nat_lit 0)
              (ih (Nat.succ k) (Nat.succ p))
              (Nat.beq (lget S (Nat.succ k)) (Nat.succ p)))
            (Nat.beq (chAt q.1 (Nat.sub q.2 (nat_lit 1))) (nat_lit 10)))
          (andB (Nat.ble (nat_lit 1) q.2) (andB (Nat.ble q.2 (nat_lit 256))
            (andB (noNL q.1 (Nat.sub q.2 (nat_lit 1)))
              (Bool.rec (motive := fun _ => Bool) (Nat.beq q.2 (nat_lit 256)) true
                (Nat.beq (chAt q.1 (Nat.sub q.2 (nat_lit 1))) (nat_lit 10)))))))
        CH (nat_lit 0) (nat_lit 0)))

@[expose] noncomputable def joinP (CH : List (Nat × Nat)) (s n : Nat) : Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat) (fun _ acc => acc)
    (fun q _ ih n acc => Bool.rec (motive := fun _ => Nat × Nat) acc
      (forceP (Nat.lor acc.1 (Nat.shiftLeft q.1 (Nat.mul (nat_lit 8) acc.2)))
        (ih (Nat.sub n (nat_lit 1))
          (Nat.lor acc.1 (Nat.shiftLeft q.1 (Nat.mul (nat_lit 8) acc.2)), Nat.add acc.2 q.2)))
      (Nat.blt (nat_lit 0) n))
    (dropP CH s) n (nat_lit 0, nat_lit 0)

@[expose] noncomputable def lineOf (CH : List (Nat × Nat)) (S : List Nat) (i : Nat) : Nat × Nat :=
  joinP CH (lget S i) (Nat.sub (lget S (Nat.succ i)) (lget S i))

end CFSG.KC.BM.Pkt

end
