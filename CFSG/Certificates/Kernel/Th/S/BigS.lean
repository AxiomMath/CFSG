module

public import CFSG.Certificates.Kernel.Th.Big
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Th.S.Hsw

public section

namespace CFSG.KC.Th.BigS

open CFSG.KC.Th CFSG.KC.Loop

@[expose] noncomputable def bitsN (J o x : Nat) : Nat :=
  Nat.land (Nat.shiftRight J o) (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1))

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec true false b

@[expose] noncomputable def rep (x s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.lor acc (Nat.shiftLeft x (Nat.mul s i))) n

@[expose] noncomputable def tmask (k : Nat) : Nat :=
  (fun s => (fun row => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft row (Nat.mul (nat_lit 256) r)))
        (Nat.beq (Nat.land r s) (nat_lit 0))) (nat_lit 256))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c acc => Bool.rec (motive := fun _ => Nat) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) c)) acc
        (Nat.beq (Nat.land c s) (nat_lit 0))) (nat_lit 256)))
  (Nat.shiftLeft (nat_lit 1) k)

@[expose] noncomputable def upper : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.sub (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 248)) (nat_lit 1))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ i)) (nat_lit 1))) (Nat.mul (nat_lit 256) i))) (nat_lit 248)

@[expose] noncomputable def constsOK (c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : Nat) : Bool :=
  andB (Nat.beq c (rep (nat_lit 1) (nat_lit 256) (nat_lit 248)))
  (andB (Nat.beq rm (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 248)) (nat_lit 1)))
  (andB (Nat.beq tm0 (tmask (nat_lit 0))) (andB (Nat.beq tm1 (tmask (nat_lit 1)))
  (andB (Nat.beq tm2 (tmask (nat_lit 2))) (andB (Nat.beq tm3 (tmask (nat_lit 3)))
  (andB (Nat.beq tm4 (tmask (nat_lit 4))) (andB (Nat.beq tm5 (tmask (nat_lit 5)))
  (andB (Nat.beq tm6 (tmask (nat_lit 6))) (andB (Nat.beq tm7 (tmask (nat_lit 7)))
  (andB (Nat.beq up upper) (andB (Nat.beq dg (rep (nat_lit 1) (nat_lit 257) (nat_lit 248)))
    (Nat.beq ONE dg))))))))))))

@[expose] noncomputable def byteAt (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def ws (b : Nat) : Bool :=
  orB (Nat.beq b (nat_lit 32)) (orB (Nat.beq b (nat_lit 9)) (orB (Nat.beq b (nat_lit 10))
    (orB (Nat.beq b (nat_lit 13)) (orB (Nat.beq b (nat_lit 11)) (Nat.beq b (nat_lit 12))))))

@[expose] noncomputable def ent2 (b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.land (Nat.sub b (nat_lit 48)) (nat_lit 1))
    (andB (Nat.ble (nat_lit 48) b) (Nat.ble b (nat_lit 57)))

@[expose] noncomputable def entBit (M k : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.add (Nat.mul (nat_lit 256) (Nat.div k (nat_lit 248))) (Nat.mod k (nat_lit 248)))) (nat_lit 1)

@[expose] noncomputable def decodeRun (F : Nat → Nat) (lb M : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun leaf _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
        (fun q ih2 S => (fun b => strictN
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
              ((fun k st => Bool.rec (motive := fun _ => Nat)
                  (Bool.rec (motive := fun _ => Nat) S (Nat.add S (nat_lit 1)) (Nat.beq b (nat_lit 10)))
                  (Bool.rec (motive := fun _ => Nat)
                    (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 2))
                      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.add S (nat_lit 2))
                        (Nat.beq (ent2 b) (entBit M k)))
                      (Nat.blt k (nat_lit 61504)))
                    S (ws b))
                  (Nat.beq st (nat_lit 1)))
                (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 1)) (Nat.land (Nat.sub S (nat_lit 1)) (nat_lit 1)))
              (Nat.blt (nat_lit 0) S))
            ih2) (byteAt (F leaf) (Nat.sub (Nat.sub lb (nat_lit 1)) q)))
        lb S) ih) Cs

@[expose] noncomputable def seedDone (c rm M S : Nat) : Bool :=
  andB (Nat.beq (Nat.land M (Nat.mul rm c)) M)
    (andB (Nat.ble (nat_lit 123010) S) (Nat.beq (Nat.land S (nat_lit 1)) (nat_lit 0)))

@[expose] noncomputable def powB (c rm ONE M e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => (fun sq => Bool.rec (motive := fun _ => Nat) sq (mulB c rm sq M)
        (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (Nat.sub nb (nat_lit 1)) i)) (nat_lit 1)) (nat_lit 1)))
      (mulB c rm acc acc)) nb

@[expose] noncomputable def regBelow (a r : Nat) : Bool := andB (Nat.blt (nat_lit 0) a) (Nat.blt a r)

@[expose] noncomputable def insOK (RB : Nat → Nat) (c rm ONE r ins : Nat) : Bool :=
  (fun k a b e => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (regBelow a r) (Nat.beq (mulB c rm (RB a) (RB r)) ONE)) (Nat.beq k (nat_lit 2)))
        (andB (regBelow a r) (andB (Nat.blt (nat_lit 0) e) (Nat.beq (RB r) (powB c rm ONE (RB a) e (nat_lit 4)))))
        (Nat.beq k (nat_lit 1)))
      (andB (regBelow a r) (andB (regBelow b r) (Nat.beq (RB r) (mulB c rm (RB a) (RB b)))))
      (Nat.beq k (nat_lit 0)))
  (Nat.land ins (nat_lit 3)) (bitsN ins (nat_lit 2) (nat_lit 11)) (bitsN ins (nat_lit 13) (nat_lit 11))
  (bitsN ins (nat_lit 24) (nat_lit 4))

@[expose] noncomputable def runSlp (RB : Nat → Nat) (c rm ONE : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S) (insOK RB c rm ONE S (bitsN J (nat_lit 0) (nat_lit 28)))))
          (ih2 (Nat.shiftRight J (nat_lit 28))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def marked (m r : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) r))

@[expose] noncomputable def runMarked (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun r m ins => (fun k a b => strictN
            (Nat.lor (Nat.succ r) (Nat.shiftLeft
              (Bool.rec (motive := fun _ => Nat) m (Nat.lor m (Nat.shiftLeft (nat_lit 1) r))
                (Bool.rec (motive := fun _ => Bool) (marked m a) (andB (marked m a) (marked m b)) (Nat.beq k (nat_lit 0))))
              (nat_lit 11)))
            (ih2 (Nat.shiftRight J (nat_lit 28))))
          (Nat.land ins (nat_lit 3)) (bitsN ins (nat_lit 2) (nat_lit 11)) (bitsN ins (nat_lit 13) (nat_lit 11)))
          (Nat.land S (nat_lit 2047)) (Nat.shiftRight S (nat_lit 11)) (bitsN J (nat_lit 0) (nat_lit 28)))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def regAt (L k : Nat) : Nat := bitsN L (Nat.mul (nat_lit 11) k) (nat_lit 11)

@[expose] noncomputable def regsIn (L n r : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (regBelow (regAt L k) r)) n

@[expose] noncomputable def allMarked (L n m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (marked m (regAt L k))) n

@[expose] noncomputable def letV (RB : Nat → Nat) (GR IR x : Nat) : Nat :=
  RB (Bool.rec (motive := fun _ => Nat) (regAt GR (Nat.shiftRight x (nat_lit 1))) (regAt IR (Nat.shiftRight x (nat_lit 1)))
    (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def relOK (RB : Nat → Nat) (c rm ONE GR IR r : Nat) : Bool :=
  (fun e => andB (Nat.blt r (nat_lit 39)) (Nat.beq ONE
    (Nat.rec (motive := fun _ => Nat) ONE
      (fun i acc => mulB c rm acc (letV RB GR IR (Nat.land (Nat.shiftRight (Nat.shiftRight e (nat_lit 12)) (Nat.mul (nat_lit 8) i)) (nat_lit 255))))
      (bitsN e (nat_lit 2) (nat_lit 10)))))
  (Hsw.sel r)

@[expose] noncomputable def relsOK (RB : Nat → Nat) (c rm ONE GR IR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih (relOK RB c rm ONE GR IR r)) (nat_lit 39)

@[expose] noncomputable def wordAB (c rm ONE A B Bi w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun i acc => (fun x => mulB c rm acc
      (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) Bi B (Nat.beq x (nat_lit 1))) A (Nat.beq x (nat_lit 0))))
    (bitsN w (Nat.mul (nat_lit 2) i) (nat_lit 2))) n

@[expose] noncomputable def primeOrder (c rm ONE M p nb : Nat) : Bool :=
  andB (Nat.beq (powB c rm ONE M p nb) ONE) (notB (Nat.beq M ONE))

@[expose] noncomputable def invOK (RB : Nat → Nat) (c rm ONE GR IR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih
    (Nat.beq (mulB c rm (RB (regAt GR g)) (RB (regAt IR g))) ONE)) (nat_lit 8)

@[expose] noncomputable def fixWOK (RB : Nat → Nat) (rm GR w1 w2 n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih
    (andB (chkInW rm w1 (RB (regAt GR g)) w1 w2) (chkInW rm w2 (RB (regAt GR g)) w1 w2))) n

@[expose] noncomputable def pwOK (RB PW : Nat → Nat) (c rm PR n p : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (Nat.rec (motive := fun _ => Bool) true (fun e ih2 => andB ih2
      (Nat.beq (PW (Nat.add (Nat.mul k (Nat.sub p (nat_lit 1))) e))
        (Bool.rec (motive := fun _ => Nat)
          (mulB c rm (PW (Nat.sub (Nat.add (Nat.mul k (Nat.sub p (nat_lit 1))) e) (nat_lit 1))) (RB (regAt PR k)))
          (RB (regAt PR k)) (Nat.beq e (nat_lit 0)))))
      (Nat.sub p (nat_lit 1)))) n

@[expose] noncomputable def rhsPc (PW : Nat → Nat) (c rm ONE n p pb x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun k acc => (fun e => Bool.rec (motive := fun _ => Nat)
      (mulB c rm acc (PW (Nat.sub (Nat.add (Nat.mul k (Nat.sub p (nat_lit 1))) e) (nat_lit 1)))) acc
      (Nat.beq e (nat_lit 0)))
    (bitsN x (Nat.mul pb k) pb)) n

@[expose] noncomputable def pcRelOK (RB PW : Nat → Nat) (c rm ONE PR n p pb i j x : Nat) : Bool :=
  andB (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
      (Bool.rec (motive := fun _ => Bool) (Nat.blt (bitsN x (Nat.mul pb k) pb) p)
        (Nat.beq (bitsN x (Nat.mul pb k) pb) (nat_lit 0)) (Nat.ble k i))) n)
    ((fun R => Bool.rec (motive := fun _ => Bool)
        (Nat.beq (mulB c rm (RB (regAt PR j)) (RB (regAt PR i))) (mulB c rm (RB (regAt PR i)) R))
        (Nat.beq (mulB c rm (PW (Nat.sub (Nat.add (Nat.mul i (Nat.sub p (nat_lit 1))) (Nat.sub p (nat_lit 1))) (nat_lit 1)))
          (RB (regAt PR i))) R)
        (Nat.beq i j))
      (rhsPc PW c rm ONE n p pb x))

@[expose] noncomputable def runPc (RB PW : Nat → Nat) (c rm ONE PR n p pb : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun i j => strictN
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
              (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 256))
                (Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 1) n)
                  (Nat.add (nat_lit 1) (Nat.add (Nat.succ i) (Nat.shiftLeft (Nat.succ i) (nat_lit 8)))) (Nat.blt (Nat.succ i) n))
                (Nat.beq (Nat.succ j) n))
              (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt i n) (andB (Nat.blt j n)
                (pcRelOK RB PW c rm ONE PR n p pb i j (bitsN J (nat_lit 0) (Nat.mul n pb)))))))
            (ih2 (Nat.shiftRight J (Nat.mul n pb))))
          (Nat.land (Nat.sub S (nat_lit 1)) (nat_lit 255)) (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 8)))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def gensPcOK (GL m PR n H : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (andB (Nat.blt (bitsN H (Nat.mul (nat_lit 5) k) (nat_lit 5)) n)
      (Nat.beq (regAt GL k) (regAt PR (bitsN H (Nat.mul (nat_lit 5) k) (nat_lit 5)))))) m

@[expose] noncomputable def runTree (RB PT : Nat → Nat) (rm PR fr to : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun k par g => strictN
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
              (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt par k) (andB (Nat.blt fr g) (andB (Nat.ble g to)
                (Nat.beq (PT k) (vecB rm (PT par) (RB (regAt PR (Nat.sub g (nat_lit 1)))))))))))
            (ih2 (Nat.shiftRight J (nat_lit 17))))
          (Nat.sub S (nat_lit 1)) (bitsN J (nat_lit 0) (nat_lit 12)) (bitsN J (nat_lit 12) (nat_lit 5)))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def baseFixed (RB : Nat → Nat) (rm PR v to n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (Bool.rec (motive := fun _ => Bool) true (Nat.beq (vecB rm v (RB (regAt PR k))) v) (Nat.ble to k))) n

@[expose] noncomputable def blocksOK (BL nb n : Nat) : Bool :=
  (fun r => andB (Nat.blt (nat_lit 0) r) (Nat.beq (Nat.sub r (nat_lit 1)) n))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun b acc => (fun fr to =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ to)
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.beq fr (Nat.sub acc (nat_lit 1))) (Nat.blt fr to))))
      (bitsN BL (Nat.mul (nat_lit 10) b) (nat_lit 5)) (bitsN BL (Nat.add (Nat.mul (nat_lit 10) b) (nat_lit 5)) (nat_lit 5))) nb)

@[expose] noncomputable def uniOK (RB : Nat → Nat) (c rm up dg Cm Ci GL m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (chkUni up dg (mulB c rm (mulB c rm Cm (RB (regAt GL k))) Ci))) m

@[expose] noncomputable def sizesOf (MD NORD n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.lor acc
    (Nat.shiftLeft (Nat.div NORD (bitsN MD (Nat.mul (nat_lit 20) (Nat.succ k)) (nat_lit 20))) (Nat.mul (nat_lit 32) k))) n

@[expose] noncomputable def planeOf (rm A Bi B root w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) root (fun i acc => (fun x => planeStep rm
      (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) B Bi (Nat.beq x (nat_lit 1))) A (Nat.beq x (nat_lit 0))) acc)
    (bitsN w (Nat.mul (nat_lit 2) i) (nat_lit 2))) n

@[expose] noncomputable def runPlanes (rm A Bi B root Cb : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun k n => strictN
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
              (andB (Nat.blt (nat_lit 0) S)
                (Nat.beq (Nat.lor (rowB rm Cb (Nat.mul (nat_lit 2) k)) (Nat.shiftLeft (rowB rm Cb (Nat.succ (Nat.mul (nat_lit 2) k))) (nat_lit 256)))
                  (planeOf rm A Bi B root (bitsN J (nat_lit 4) (Nat.mul (nat_lit 2) n)) n))))
            (ih2 (Nat.shiftRight J (Nat.add (nat_lit 4) (Nat.mul (nat_lit 2) n)))))
          (Nat.sub S (nat_lit 1)) (bitsN J (nat_lit 0) (nat_lit 4)))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def runBfs (rm G : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun i j sn => strictN
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.add S (Nat.shiftLeft (nat_lit 2) j))
              (andB (Nat.blt (nat_lit 0) S) (andB (marked sn i) (andB (notB (marked sn j)) (chkEdge rm G i j)))))
            (ih2 (Nat.shiftRight J (nat_lit 14))))
          (bitsN J (nat_lit 0) (nat_lit 7)) (bitsN J (nat_lit 7) (nat_lit 7)) (Nat.shiftRight S (nat_lit 1)))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def forcedV (g a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Nat.add (Nat.add (Nat.add (Nat.mul (nat_lit 6) (forced g a (nat_lit 6))) (Nat.mul (nat_lit 7) (forced g a (nat_lit 7))))
        (Nat.add (Nat.mul (nat_lit 9) (forced g a (nat_lit 9))) (Nat.mul (nat_lit 11) (forced g a (nat_lit 11)))))
      (Nat.add (Nat.mul (nat_lit 13) (forced g a (nat_lit 13))) (Nat.mul (nat_lit 14) (forced g a (nat_lit 14)))))
    (Nat.beq (nForced g a) (nat_lit 1))

@[expose] noncomputable def propVertex (rm G i S : Nat) : Nat :=
  (fun asg sn => Bool.rec (motive := fun _ => Nat) (Nat.lor S (Nat.shiftLeft (nat_lit 2) (nat_lit 620)))
    ((fun r0 r1 ai => Nat.rec (motive := fun _ => Nat) S (fun j T =>
        Bool.rec (motive := fun _ => Nat)
          ((fun g => Bool.rec (motive := fun _ => Nat) T
              ((fun v => Bool.rec (motive := fun _ => Nat) (Nat.lor T (Nat.shiftLeft (nat_lit 2) (nat_lit 620)))
                  (Bool.rec (motive := fun _ => Nat)
                    (Nat.lor (Nat.lor T (Nat.shiftLeft v (Nat.mul (nat_lit 4) j))) (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 496) j)))
                    (Bool.rec (motive := fun _ => Nat) (Nat.lor T (Nat.shiftLeft (nat_lit 1) (nat_lit 620))) T
                      (Nat.beq (bitsN T (Nat.mul (nat_lit 4) j) (nat_lit 4)) v))
                    (marked (bitsN T (nat_lit 496) (nat_lit 124)) j))
                  (Nat.blt (nat_lit 0) v))
                (forcedV g ai))
              (Nat.beq (det2 g) (nat_lit 1)))
            (blk r0 r1 j))
          T
          (orB (Nat.beq j i) (Nat.blt (nat_lit 0) (Nat.shiftRight T (nat_lit 620)))))
        (nat_lit 124))
      (rowB rm G (Nat.mul (nat_lit 2) i)) (rowB rm G (Nat.succ (Nat.mul (nat_lit 2) i))) (bitsN asg (Nat.mul (nat_lit 4) i) (nat_lit 4)))
    (marked sn i))
  (bitsN S (nat_lit 0) (nat_lit 496)) (bitsN S (nat_lit 496) (nat_lit 124))

@[expose] noncomputable def propRun (rm G a0 Q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => strictN (Bool.rec (motive := fun _ => Nat) S (propVertex rm G (bitsN J (nat_lit 0) (nat_lit 7)) S)
        (Nat.beq (Nat.shiftRight S (nat_lit 620)) (nat_lit 0)))
      (ih (Nat.shiftRight J (nat_lit 7))))
    (Nat.land Q (nat_lit 255)) (Nat.shiftRight Q (nat_lit 8))
    (Nat.lor a0 (Nat.shiftLeft (nat_lit 1) (nat_lit 496)))

@[expose] noncomputable def propConflict (rm G a0 Q : Nat) : Bool :=
  Nat.beq (Nat.shiftRight (propRun rm G a0 Q) (nat_lit 620)) (nat_lit 1)

@[expose] noncomputable def propConstant (rm G a0 Q : Nat) : Bool :=
  (fun S => andB (Nat.beq (Nat.shiftRight S (nat_lit 620)) (nat_lit 0))
    (andB (Nat.beq (bitsN S (nat_lit 496) (nat_lit 124)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 124)) (nat_lit 1)))
      (andB (Nat.beq (bitsN S (nat_lit 0) (nat_lit 496)) (Nat.mul a0 (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 496)) (nat_lit 1)) (nat_lit 15))))
        (allPreserved rm G a0 (nat_lit 124)))))
  (propRun rm G a0 Q)

end CFSG.KC.Th.BigS

end
