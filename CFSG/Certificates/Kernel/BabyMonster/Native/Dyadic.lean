module

public import CFSG.Certificates.Kernel.BabyMonster.Render
public import CFSG.Certificates.Kernel.BabyMonster.Native.Small

public section

namespace CFSG.KC.BM

@[expose] noncomputable def dyMask (m : Nat) : Nat := rep (Nat.sub m (nat_lit 1)) (nat_lit 16) (nat_lit 4371)

@[expose] noncomputable def dyFail : Nat := Nat.shiftLeft (nat_lit 1) (nat_lit 5000)

@[expose] noncomputable def dyElim (m : Nat) (Bs : List (List Nat)) (k v : Nat) : Nat :=
  (fun M => List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun v out _ bad => Bool.rec (motive := fun _ => Nat) dyFail
      (Bool.rec (motive := fun _ => Nat) dyFail out (Nat.beq bad (nat_lit 0))) (Nat.beq v (nat_lit 0)))
    (fun blk _ ih v out j bad =>
      Bool.rec (motive := fun _ => Nat)
        (List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun v out j bad => ih v out j bad)
          (fun b _ ih2 v out j bad =>
            Bool.rec (motive := fun _ => Nat)
              (ih2 v out (Nat.succ j) bad)
              ((fun x => Bool.rec (motive := fun _ => Nat)
                  ((fun p => (fun q => ih2
                      (Nat.shiftRight (Nat.land (Nat.add v (Nat.mul (Nat.sub m q) b)) M) (nat_lit 16))
                      (Nat.lor out (Nat.shiftLeft (Nat.land q (nat_lit 1)) j))
                      (Nat.succ j)
                      (Nat.lor bad (Nat.land x (Nat.sub p (nat_lit 1)))))
                    (Nat.div x p)) (Nat.land b (nat_lit 65535)))
                  (ih2 (Nat.shiftRight v (nat_lit 16)) out (Nat.succ j) bad)
                  (Nat.beq x (nat_lit 0)))
                (Nat.land v (nat_lit 65535)))
              (Nat.ble k j))
          blk v out j bad)
        (List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun v out j bad => ih v out j bad)
          (fun b _ ih2 v out j bad =>
            (fun x => Bool.rec (motive := fun _ => Nat)
                ((fun p => (fun q => ih2
                    (Nat.shiftRight (Nat.land (Nat.add v (Nat.mul (Nat.sub m q) b)) M) (nat_lit 16))
                    (Nat.lor out (Nat.shiftLeft (Nat.land q (nat_lit 1)) j))
                    (Nat.succ j)
                    (Nat.lor bad (Nat.land x (Nat.sub p (nat_lit 1)))))
                  (Nat.div x p)) (Nat.land b (nat_lit 65535)))
                (ih2 (Nat.shiftRight v (nat_lit 16)) out (Nat.succ j) bad)
                (Nat.beq x (nat_lit 0)))
              (Nat.land v (nat_lit 65535)))
          blk v out j bad)
        (Nat.ble k j))
    Bs v (nat_lit 0) (nat_lit 0) (nat_lit 0)) (dyMask m)

@[expose] noncomputable def dyRowOK (n j b : Nat) : Bool :=
  (fun p => andB (andB (Nat.blt (nat_lit 0) p) (andB (Nat.ble p (nat_lit 128))
      (Nat.beq (Nat.land p (Nat.sub p (nat_lit 1))) (nat_lit 0))))
    (andB (Nat.beq (Nat.shiftRight b (Nat.mul (nat_lit 16) (Nat.sub n j))) (nat_lit 0))
      (Nat.beq (Nat.land (Nat.shiftRight b (nat_lit 16)) (dyMask (nat_lit 65536)))
        (Nat.land (Nat.shiftRight b (nat_lit 16)) (dyMask (nat_lit 128))))))
    (Nat.land b (nat_lit 65535))

@[expose] noncomputable def dyElim32 (m : Nat) (Bs : List (List Nat)) (k v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun v out _ => Bool.rec (motive := fun _ => Nat) dyFail out (Nat.beq v (nat_lit 0)))
    (fun blk _ ih v out j =>
      List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun v out j => ih v out j)
        (fun b _ ih2 v out j =>
          Bool.rec (motive := fun _ => Nat)
            ((fun x => Bool.rec (motive := fun _ => Nat)
                ((fun p => Bool.rec (motive := fun _ => Nat) dyFail
                    ((fun q => forceB (Nat.shiftRight (Nat.add v (Nat.mul (Nat.sub m q) b)) (nat_lit 32))
                        (fun v' => forceB (Nat.lor out (Nat.shiftLeft (Nat.land q (nat_lit 1)) j))
                          (fun out' => ih2 v' out' (Nat.succ j))))
                      (Nat.div x p))
                    (Nat.beq (Nat.land x (Nat.sub p (nat_lit 1))) (nat_lit 0)))
                  (Nat.land b (nat_lit 4294967295)))
                (forceB (Nat.shiftRight v (nat_lit 32)) (fun v' => ih2 v' out (Nat.succ j)))
                (Nat.beq x (nat_lit 0)))
              (Nat.mod (Nat.land v (nat_lit 4294967295)) m))
            (ih2 v out (Nat.succ j))
            (Nat.blt j k))
        blk v out j)
    Bs v (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def labels0 (N : Nat) : Nat :=
  Nat.div (Nat.add (nat_lit 65536) (Nat.mul (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) N))
      (Nat.sub (Nat.mul (Nat.sub N (nat_lit 1)) (nat_lit 65536)) N)))
    (nat_lit 4294836225)

@[expose] noncomputable def labels (lo hi : Nat) : Nat := Nat.sub (labels0 hi) (labels0 lo)

@[expose] noncomputable def benes (Ms Ds : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ x => x)
    (fun M _ ih Ds x => List.rec (motive := fun _ => Nat) x
      (fun D Ds' _ => forceB (Nat.land (Nat.xor (Nat.shiftRight x D) x) M) (fun t =>
        forceB (Nat.xor x (Nat.xor t (Nat.shiftLeft t D))) (fun x' => ih Ds' x'))) Ds)
    Ms Ds x

@[expose] noncomputable def negF (NM v : Nat) : Nat :=
  (fun w => Nat.add (Nat.sub v w)
      (Nat.land (Nat.sub (Nat.land NM (rep (nat_lit 256) (nat_lit 16) (nat_lit 4371))) w) (dyMask (nat_lit 256))))
    (Nat.land v NM)

@[expose] noncomputable def benesOK (Ms Ds : List Nat) (T NM : Nat) : Bool :=
  Nat.beq (benes Ms Ds (Nat.add T (labels (nat_lit 4371) (nat_lit 8192))))
    (Nat.add (labels (nat_lit 0) (nat_lit 8192)) (Nat.land NM (rep (nat_lit 8192) (nat_lit 16) (nat_lit 4371))))

@[expose] noncomputable def negMaskOK (NM : Nat) : Bool :=
  andB (Nat.beq (Nat.land NM (dyMask (nat_lit 65536))) NM)
    (Nat.beq (Nat.mul (Nat.land NM (rep (nat_lit 1) (nat_lit 16) (nat_lit 4371))) (nat_lit 65535)) NM)

@[expose] noncomputable def monoImg (Ms Ds : List Nat) (NM i b : Nat) : Nat :=
  negF NM (benes Ms Ds (Nat.shiftLeft b (Nat.mul (nat_lit 16) i)))

@[expose] noncomputable def dropN (k : Nat) (L : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun L => L)
    (fun _ ih L => ih (List.rec (motive := fun _ => List Nat) List.nil (fun _ xs _ => xs) L)) k L

@[expose] noncomputable def oneF (S : Nat) : Nat := Nat.land S (rep (nat_lit 1) (nat_lit 16) (nat_lit 4371))

@[expose] noncomputable def colorStep (C : List Nat) (Ds : List Nat) (x : Nat) : Nat :=
  (fun S2 S4 S8 N2 N4 N8 => benes (dropN (nat_lit 6) C) Ds
      (Nat.add (Nat.add (Nat.add (Nat.mul (nat_lit 2) (Nat.land x S2)) (Nat.mul (nat_lit 4) (Nat.land x S4)))
          (Nat.mul (nat_lit 8) (Nat.land x S8)))
        (Nat.add (Nat.add (Nat.sub (Nat.mul (nat_lit 2048) (oneF N2)) (Nat.mul (nat_lit 2) (Nat.land x N2)))
            (Nat.sub (Nat.mul (nat_lit 2048) (oneF N4)) (Nat.mul (nat_lit 4) (Nat.land x N4))))
          (Nat.sub (Nat.mul (nat_lit 2048) (oneF N8)) (Nat.mul (nat_lit 8) (Nat.land x N8))))))
    (nthN C 0) (nthN C 1) (nthN C 2) (nthN C 3) (nthN C 4) (nthN C 5)

@[expose] noncomputable def colorImg (Cs : List (List Nat)) (Ds : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun C _ ih acc => forceB (Nat.add acc (colorStep C Ds x)) (fun a => ih a)) Cs (nat_lit 0)

@[expose] noncomputable def takeN (k : Nat) (L : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun _ ih L => List.rec (motive := fun _ => List Nat) List.nil (fun x xs _ => List.cons x (ih xs)) L) k L

@[expose] noncomputable def colorRowsL (Cs : List (List Nat)) (Ds : List Nat) (j0 : Nat) (L : List Nat) : Bool :=
  Nat.blt (nat_lit 0) (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ ok => ok)
      (fun r _ ih j ok => forceB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) ok
          (Nat.beq (Nat.land (colorImg Cs Ds (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) j)))
            (rep (nat_lit 2047) (nat_lit 16) (nat_lit 4371))) r))
        (fun ok' => forceB (Nat.succ j) (fun j' => ih j' ok'))) L j0 (nat_lit 1))

@[expose] noncomputable def colorRed (v : Nat) : Nat :=
  (fun w => Bool.rec (motive := fun _ => Nat) dyFail (Nat.shiftRight w (nat_lit 3))
      (Nat.beq (Nat.land w (rep (nat_lit 7) (nat_lit 16) (nat_lit 4371))) (nat_lit 0)))
    (Nat.land v (rep (nat_lit 2047) (nat_lit 16) (nat_lit 4371)))

@[expose] noncomputable def dyBasisOK (n : Nat) (Bs : List (List Nat)) (j : Nat) : Bool :=
  Nat.blt (nat_lit 0) (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ ok => ok)
    (fun blk _ ih j ok => List.rec (motive := fun _ => Nat → Nat → Nat) (fun j ok => ih j ok)
      (fun b _ ih2 j ok => forceB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) ok (dyRowOK n j b))
        (fun ok' => ih2 (Nat.succ j) ok')) blk j ok)
    Bs j (nat_lit 1))

end CFSG.KC.BM

end
