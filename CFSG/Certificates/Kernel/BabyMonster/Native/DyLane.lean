module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Dyadic
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck

public section

namespace CFSG.KC.BM

open CFSG.KC.BM.Lat

@[expose] noncomputable def lnStage (K D x : Nat) : Nat :=
  (fun a => Nat.add a (Nat.shiftLeft (Nat.sub x a) D)) (Nat.land x K)

@[expose] noncomputable def lnSpr (Ks : List Nat) (D x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun K _ ih D x => forceB (lnStage K D x) (fun x' => ih (Nat.shiftRight D (nat_lit 1)) x'))
    Ks D x

@[expose] noncomputable def lnK (w W b : Nat) : Nat :=
  rep (onesN (Nat.mul w (Nat.shiftLeft (nat_lit 1) b))) (Nat.mul W (Nat.shiftLeft (nat_lit 1) (Nat.succ b)))
    (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 12) b))

@[expose] noncomputable def lnKs (w W : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun b acc => List.cons (lnK w W b) acc) (nat_lit 13)

@[expose] noncomputable def lnDs : List Nat :=
  [65536, 32768, 16384, 8192, 4096, 2048, 1024, 512, 256, 128, 64, 32, 16, 32, 64, 128, 256, 512,
    1024, 2048, 4096, 8192, 16384, 32768, 65536]

@[expose] noncomputable def lnMonoF (Bs : List (List Nat)) (Ms : List Nat) (NM i : Nat) : Nat :=
  monoImg Ms lnDs NM i (recOf Bs i)

@[expose] noncomputable def lnColF (Bs : List (List Nat)) (Cs : List (List Nat)) (i : Nat) : Nat :=
  colorRed (colorImg Cs lnDs (Nat.shiftLeft (recOf Bs i) (Nat.mul (nat_lit 16) i)))

@[expose] noncomputable def lnOne : Nat := rep (nat_lit 1) (nat_lit 16) (nat_lit 16)

@[expose] noncomputable def lnSM0 : Nat := rep (nat_lit 65535) (nat_lit 256) (nat_lit 4371)

@[expose] noncomputable def lnMask (m : Nat) : Nat :=
  rep (Nat.sub m (nat_lit 1)) (nat_lit 16) (Nat.mul (nat_lit 16) (nat_lit 4371))

@[expose] noncomputable def lnLM : Nat := onesN (nat_lit 256)

@[expose] noncomputable def lnElimK (ONE MQ SM0 MASK LMr : Nat) (SS : List (List Nat)) (Y CE : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun Y CE bad => Nat.lor (Nat.lor bad Y) CE)
    (fun blk _ ih Y CE bad => List.rec (motive := fun _ => Nat) (nat_lit 1)
      (fun S ps _ => List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
        (fun _ Y CE bad => ih Y CE bad)
        (fun p _ ih2 sh Y CE bad =>
          (fun x => (fun Q =>
            forceB (Nat.shiftRight (Nat.land (Nat.add Y (Nat.mul (Nat.sub MQ Q)
                (Nat.land (Nat.shiftRight S sh) SM0))) MASK) (nat_lit 256)) (fun Y' =>
              forceB (Nat.lor (Nat.lor bad (Nat.land x (Nat.mul (Nat.sub p (nat_lit 1)) ONE)))
                  (Nat.xor (Nat.land Q ONE) (Nat.land CE LMr))) (fun bad' =>
                forceB (Nat.shiftRight CE (nat_lit 256)) (fun CE' =>
                  ih2 (Nat.add sh (nat_lit 272)) Y' CE' bad'))))
            (Nat.div x p)) (Nat.land Y LMr))
        ps (nat_lit 0) Y CE bad) blk)
    SS Y CE (nat_lit 0)

@[expose] noncomputable def lnElim (m : Nat) (SS : List (List Nat)) (Y CE : Nat) : Nat :=
  forceB lnOne (fun ONE => forceB (Nat.mul m ONE) (fun MQ => forceB lnSM0 (fun SM0 =>
    forceB (lnMask m) (fun MASK => forceB lnLM (fun LMr => lnElimK ONE MQ SM0 MASK LMr SS Y CE)))))

@[expose] noncomputable def lnD (w W : Nat) : Nat := Nat.mul (Nat.sub W w) (nat_lit 4096)

@[expose] noncomputable def lnDrop (k : Nat) (L : List (List Nat)) : List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun L => L)
    (fun _ ih L => ih (List.rec (motive := fun _ => List (List Nat)) List.nil (fun _ xs _ => xs) L)) k L

@[expose] noncomputable def lnFail : Nat := Nat.shiftLeft (nat_lit 512) (nat_lit 69936)

@[expose] noncomputable def lnLeaf (m : Nat) (K : List Nat) (F R : Nat → Nat) (B j i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) lnFail
    (Nat.add (F i) (Nat.shiftLeft (lnSpr K (lnD (nat_lit 1) (nat_lit 16)) (Nat.shiftRight (R i) j)) (nat_lit 8)))
    (andB (andB (Nat.beq (Nat.land (F i) (dyMask m)) (F i)) (Nat.blt (F i) B))
      (Nat.blt (R i) (Nat.shiftLeft (nat_lit 1) (nat_lit 4371))))

@[expose] noncomputable def lnQ (Ks : List Nat) (w a b : Nat) : Nat :=
  (fun D => Nat.add (lnSpr Ks D a) (Nat.shiftLeft (lnSpr Ks D b) w)) (lnD w (Nat.mul (nat_lit 2) w))

@[expose] noncomputable def lnT (KK : List (List Nat)) (U : Nat → Nat) (l : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) U
    (fun l ih i => lnQ (nthLL KK (Nat.succ l)) (Nat.shiftLeft (nat_lit 16) l) (ih i)
      (ih (Nat.add i (Nat.shiftLeft (nat_lit 1) l)))) l

@[expose] noncomputable def lnKK : List (List Nat) :=
  [lnKs (nat_lit 1) (nat_lit 16), lnKs (nat_lit 16) (nat_lit 32), lnKs (nat_lit 32) (nat_lit 64),
    lnKs (nat_lit 64) (nat_lit 128), lnKs (nat_lit 128) (nat_lit 256)]

@[expose] noncomputable def lnMaskP (m : Nat) : Nat :=
  rep (Nat.add (Nat.sub m (nat_lit 1)) (nat_lit 256)) (nat_lit 16) (Nat.mul (nat_lit 16) (nat_lit 4371))

@[expose] noncomputable def lnOnes : Nat := rep (nat_lit 1) (nat_lit 16) (Nat.mul (nat_lit 16) (nat_lit 4371))

@[expose] noncomputable def lnSt (m : Nat) (KK SS : List (List Nat)) (F R : Nat → Nat) (s k : Nat) : Bool :=
  (fun j => (fun Z => andB (Nat.beq (Nat.land Z (lnMaskP m)) Z)
      (Nat.beq (lnElim m (lnDrop s SS) (Nat.land Z (lnMask m)) (Nat.land (Nat.shiftRight Z (nat_lit 8)) lnOnes))
        (nat_lit 0)))
    (lnT KK (lnLeaf m (nthLL KK (nat_lit 0)) F R
        (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) (Nat.sub (nat_lit 4371) j))) j)
      (nat_lit 4) (Nat.mul (nat_lit 16) k)))
    (Nat.mul (nat_lit 16) s)

@[expose] noncomputable def lnContV (Bs : List (List Nat)) (i : Nat) : Nat :=
  Nat.shiftRight (Nat.land (Nat.mul (Nat.div (nat_lit 128) (Nat.land (recOf Bs i) (nat_lit 65535)))
    (recOf Bs i)) (dyMask (nat_lit 128))) (nat_lit 16)

@[expose] noncomputable def lnContF (Bs : List (List Nat)) (i : Nat) : Nat :=
  Nat.shiftLeft (lnContV Bs i) (Nat.mul (nat_lit 16) (Nat.add (Nat.mod i (nat_lit 16)) (nat_lit 1)))

@[expose] noncomputable def lnRowsOK (Bs : List (List Nat)) (S : Nat) (Ks : List Nat) (D : Nat) :
    List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun p _ ih j sh => andB (andB (Nat.beq p (Nat.land (recOf Bs j) (nat_lit 65535)))
        (Nat.beq (Nat.land (Nat.shiftRight S sh) lnSM0) (lnSpr Ks D (recOf Bs j))))
      (ih (Nat.succ j) (Nat.add sh (nat_lit 272))))

@[expose] noncomputable def lnRows (s : Nat) : Nat :=
  (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 16) r (Nat.ble r (nat_lit 16)))
    (Nat.sub (nat_lit 4371) (Nat.mul (nat_lit 16) s))

@[expose] noncomputable def lnStripOK (Bs SS : List (List Nat)) (s : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun S ps _ => andB (Nat.beq (lenL ps) (lnRows s))
      (lnRowsOK Bs S (lnKs (nat_lit 16) (nat_lit 256)) (lnD (nat_lit 16) (nat_lit 256)) ps
        (Nat.mul (nat_lit 16) s) (nat_lit 0)))
    (nthLL SS s)

@[expose] noncomputable def lnCont (KK Bs SS : List (List Nat)) (R : Nat → Nat) (k : Nat) : Bool :=
  lnSt (nat_lit 128) KK SS (lnContF Bs) R k k

@[expose] noncomputable def lnEqL : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun a _ ih L => List.rec (motive := fun _ => Bool) false (fun b L' _ => andB (Nat.beq a b) (ih L')) L)

@[expose] noncomputable def lnEqLL : List (List Nat) → List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun a _ ih L => List.rec (motive := fun _ => Bool) false (fun b L' _ => andB (lnEqL a b) (ih L')) L)

@[expose] noncomputable def lnFlipR (R : Nat → Nat) (b i : Nat) : Nat :=
  Nat.xor (R i) (Nat.shiftLeft (nat_lit 1) b)

end CFSG.KC.BM

end
