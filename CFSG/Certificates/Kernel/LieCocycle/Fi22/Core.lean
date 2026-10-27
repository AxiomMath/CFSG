module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KLC.Fi22

open CFSG.KC.Loop

@[expose] noncomputable def sN (v : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def sB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a
@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def maskN (w : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)

@[expose] noncomputable def bt (x i : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def fw (X w k : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul w k)) (maskN w)

@[expose] noncomputable def M4096 : Nat := maskN (nat_lit 4096)

@[expose] noncomputable def iterN (c : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun i ih s => sN (f (Nat.sub (Nat.sub c (nat_lit 1)) i) s) ih) c s

@[expose] noncomputable def allLt (m : Nat) (f : Nat → Bool) : Bool :=
  allBelow m (Nat.add (Nat.shiftRight m (nat_lit 6)) (nat_lit 1)) f

@[expose] noncomputable def fsplitI (cb h : Nat) : Nat → Nat → ((Nat → Nat) → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → ((Nat → Nat) → Bool) → Bool)
    (fun X base k => sB (Nat.lor (Nat.shiftLeft X (nat_lit 16)) base) (fun x => k (fun _ => x)))
    (fun j ih X base k => sB X (fun X =>
      sB (Nat.shiftLeft cb j) (fun w =>
        ih (Nat.land X (maskN w)) base (fun f0 =>
          ih (Nat.shiftRight X w) (Nat.add base (Nat.shiftLeft (nat_lit 1) j)) (fun f1 =>
            k (fun i => Bool.rec (motive := fun _ => Nat) (f0 i) (f1 i)
              (Nat.blt (nat_lit 0) (Nat.land i (Nat.shiftLeft (nat_lit 1) j))))))))) h

@[expose] noncomputable def fsplit (cb h : Nat) (X : Nat) (k : (Nat → Nat) → Bool) : Bool :=
  fsplitI cb h X (nat_lit 0) k

@[expose] noncomputable def ent (F : Nat → Nat) (p : Nat) : Nat :=
  sN (Nat.shiftRight p (nat_lit 6)) (fun c =>
    Nat.land (Nat.shiftRight (F c)
      (Nat.add (nat_lit 16) (Nat.shiftLeft (Nat.land p (nat_lit 63)) (nat_lit 4)))) (nat_lit 65535))

@[expose] noncomputable def rowAt (F : Nat → Nat) (u : Nat) : Nat :=
  sN (Nat.shiftRight u (nat_lit 4)) (fun c =>
    Nat.land (Nat.shiftRight (F c)
      (Nat.add (nat_lit 16) (Nat.shiftLeft (Nat.land u (nat_lit 15)) (nat_lit 12)))) M4096)

@[expose] noncomputable def stageDist (s : Nat) : Nat :=
  Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.sub (nat_lit 11) s) (Nat.sub s (nat_lit 11)))

@[expose] noncomputable def nwMask (NW s : Nat) : Nat :=
  Nat.land (Nat.shiftRight NW (Nat.shiftLeft s (nat_lit 12))) M4096

@[expose] noncomputable def stage (X m d : Nat) : Nat :=
  sN (Nat.land (Nat.xor X (Nat.shiftRight X d)) m) (fun t => Nat.xor X (Nat.lor t (Nat.shiftLeft t d)))

@[expose] noncomputable def applyNW (NW R X : Nat) : Nat :=
  iterN (nat_lit 23) (fun s Y => stage Y (Nat.mul (nwMask NW s) R) (stageDist s)) X

@[expose] noncomputable def applyInvNW (NW R X : Nat) : Nat :=
  iterN (nat_lit 23) (fun s Y =>
    stage Y (Nat.mul (nwMask NW (Nat.sub (nat_lit 22) s)) R) (stageDist (Nat.sub (nat_lit 22) s))) X

@[expose] noncomputable def coord (j : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (maskN (Nat.shiftLeft (nat_lit 1) j)) (Nat.shiftLeft (nat_lit 1) j))
    (Nat.div M4096 (maskN (Nat.shiftLeft (nat_lit 1) (Nat.add j (nat_lit 1)))))

@[expose] noncomputable def dilMask (k : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (maskN (Nat.shiftLeft (nat_lit 1) k)) (Nat.shiftLeft (nat_lit 1) k))
    (Nat.div (maskN (nat_lit 65536)) (maskN (Nat.shiftLeft (nat_lit 1) (Nat.add k (nat_lit 5)))))

@[expose] noncomputable def dil (x : Nat) : Nat :=
  iterN (nat_lit 12) (fun i y => (fun k => sN (Nat.land y (dilMask k)) (fun h =>
      Nat.lor (Nat.xor y h) (Nat.shiftLeft h (Nat.mul (nat_lit 15) (Nat.shiftLeft (nat_lit 1) k)))))
    (Nat.sub (nat_lit 11) i)) x

@[expose] noncomputable def arrOf (pl : Nat → Nat) : Nat :=
  iterN (nat_lit 12) (fun j acc => Nat.lor acc (Nat.shiftLeft (dil (pl j)) j)) (nat_lit 0)

@[expose] noncomputable def arrNW (NW : Nat) : Nat := arrOf (fun j => applyNW NW (nat_lit 1) (coord j))

@[expose] noncomputable def arrInvNW (NW : Nat) : Nat := arrOf (fun j => applyInvNW NW (nat_lit 1) (coord j))

@[expose] noncomputable def REP : Nat :=
  Nat.div (maskN (nat_lit 14376960)) M4096

@[expose] noncomputable def hd (h x : Nat) : Nat :=
  Nat.lor (Nat.xor x (Nat.land x (nat_lit 4294967295))) h

@[expose] noncomputable def zeroPlanes (h : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun _ ih => List.cons h ih) (nat_lit 10)

@[expose] noncomputable def addPl (h : Nat) (L : List Nat) : Nat → (List Nat → Nat) → Nat :=
  List.rec (motive := fun _ => Nat → (List Nat → Nat) → Nat) (fun _ k => k List.nil)
    (fun P rest ih x k => Bool.rec (motive := fun _ => Nat)
      (sN (hd h (Nat.xor P x)) (fun Q => ih (Nat.land P x) (fun rest' => k (List.cons Q rest'))))
      (k (List.cons P rest)) (Nat.beq x (nat_lit 0))) L

@[expose] noncomputable def keysK (FS FI FT FM : Nat → Nat) (a r cnt : Nat) :
    Nat → List Nat → (Nat → List Nat → Nat) → Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → (Nat → List Nat → Nat) → Nat) (fun T L k => k T L)
    (fun i ih T L k => sN (Nat.add a (Nat.sub (Nat.sub cnt (nat_lit 1)) i)) (fun p => sN (ent FS p) (fun u =>
      (fun h => sN (hd h (Nat.lor T (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 32) (ent FI (ent FT u)))))) (fun T' =>
        addPl h L (Nat.shiftLeft (rowAt FM u) (nat_lit 32)) (fun L' => ih T' L' k)))
      (Nat.lor (Nat.shiftLeft r (nat_lit 16)) (Nat.add p (nat_lit 1)))))) cnt

@[expose] noncomputable def keysOf (FS FI FT FM : Nat → Nat) (a b r : Nat) (k : Nat → List Nat → Nat) : Nat :=
  keysK FS FI FT FM a r (Nat.sub b a) (Nat.shiftLeft r (nat_lit 16)) (zeroPlanes (Nat.shiftLeft r (nat_lit 16))) k

@[expose] noncomputable def eqPl (P NS : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.xor P (Nat.shiftLeft P (nat_lit 1))) (Nat.shiftLeft NS (nat_lit 32))) (nat_lit 0)

@[expose] noncomputable def eqCheck (T : Nat) (L : List Nat) (NS : Nat) : Bool :=
  andB (eqPl T NS) (List.rec (motive := fun _ => Bool) true (fun P _ ih => andB (eqPl P NS) ih) L)

@[expose] noncomputable def ltCheck (T : Nat) (L : List Nat) (DB : Nat) : Bool :=
  (fun step => List.rec (motive := fun _ => (Nat → Nat → Bool) → Bool)
      (fun k => k (maskN (nat_lit 4200)) (nat_lit 0))
      (fun P _ ih k => ih (fun eq lt => step P eq lt k)) L
      (fun eq lt => step T eq lt (fun _ lt' =>
        Nat.beq (Nat.land (Nat.shiftLeft DB (nat_lit 32)) lt') (Nat.shiftLeft DB (nat_lit 32)))))
    (fun P eq lt k =>
      sB (Nat.lor lt (Nat.land eq (Nat.land P (Nat.xor (Nat.shiftLeft P (nat_lit 1)) (maskN (nat_lit 4200)))))) (fun lt' =>
        sB (Nat.land eq (Nat.xor (Nat.xor (Nat.shiftLeft P (nat_lit 1)) P) (maskN (nat_lit 4200)))) (fun eq' => k eq' lt')))

@[expose] noncomputable def tdS (TD i : Nat) : Nat := Nat.land (Nat.shiftRight TD (Nat.mul (nat_lit 24) i)) (nat_lit 4095)
@[expose] noncomputable def tdE (TD i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TD (Nat.add (Nat.mul (nat_lit 24) i) (nat_lit 12))) (nat_lit 4095)

@[expose] noncomputable def isCell (S n c e : Nat) : Bool :=
  andB (Nat.blt c e) (andB (Nat.ble e n) (andB (bt S c) (andB (orB (Nat.beq e n) (bt S e))
    (Nat.beq (Nat.land (Nat.shiftRight S (Nat.add c (nat_lit 1))) (maskN (Nat.sub (Nat.sub e c) (nat_lit 1))))
      (nat_lit 0)))))

@[expose] noncomputable def initOk (TD m S n : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) m) (andB (Nat.beq (tdS TD (nat_lit 0)) (nat_lit 0))
    (andB (Nat.beq (tdE TD (Nat.sub m (nat_lit 1))) n)
      (allLt m (fun i => andB (isCell S n (tdS TD i) (tdE TD i))
        (orB (Nat.beq i (nat_lit 0)) (Nat.beq (tdS TD i) (tdE TD (Nat.sub i (nat_lit 1)))))))))

@[expose] noncomputable def appendOk (TD len k S' DB n : Nat) : Bool :=
  andB (allLt k (fun i => sB (tdS TD (Nat.add len i)) (fun c => sB (tdE TD (Nat.add len i)) (fun e =>
      andB (isCell S' n c e) (andB (orB (bt DB c) (bt DB e))
        (orB (Nat.beq i (nat_lit 0)) (Nat.blt (tdS TD (Nat.sub (Nat.add len i) (nat_lit 1))) c)))))))
    (sB (sumBelow k (Nat.add (Nat.shiftRight k (nat_lit 6)) (nat_lit 1)) (fun i =>
        Nat.sub (Nat.shiftLeft (nat_lit 1) (tdE TD (Nat.add len i)))
          (Nat.shiftLeft (nat_lit 1) (tdS TD (Nat.add len i))))) (fun U =>
      andB (Nat.beq (Nat.land DB U) DB) (Nat.beq (Nat.land DB (Nat.shiftLeft U (nat_lit 1))) DB)))

@[expose] noncomputable def stS (st : Nat) : Nat := Nat.land (Nat.shiftRight st (nat_lit 16)) M4096
@[expose] noncomputable def stL (st : Nat) : Nat := Nat.land (Nat.shiftRight st (nat_lit 4112)) (nat_lit 65535)
@[expose] noncomputable def stJ (st : Nat) : Nat := Nat.shiftRight st (nat_lit 4128)
@[expose] noncomputable def mkSt (r S l j : Nat) : Nat :=
  Nat.lor r (Nat.lor (Nat.shiftLeft S (nat_lit 16))
    (Nat.lor (Nat.shiftLeft l (nat_lit 4112)) (Nat.shiftLeft j (nat_lit 4128))))

@[expose] noncomputable def dBits (DL ch : Nat) : Nat :=
  Nat.shiftRight (iterN (fw ch (nat_lit 16) (nat_lit 3)) (fun i x =>
    Nat.lor (Nat.lor (Nat.xor x (Nat.land x (nat_lit 65535)))
        (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 16) (fw DL (nat_lit 12) (Nat.add (fw ch (nat_lit 16) (nat_lit 2)) i)))))
      (Nat.add i (nat_lit 1))) (nat_lit 0)) (nat_lit 16)

@[expose] noncomputable def roundStep (FS FI FT FM : Nat → Nat) (n TD CHL DL : Nat) (r st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (sN (stS st) (fun S => sN (stL st) (fun len => sN (stJ st) (fun j =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (keysOf FS FI FT FM (tdS TD r) (tdE TD r) r (fun T L =>
          sN (fw CHL (nat_lit 64) j) (fun ch =>
            Bool.rec (motive := fun _ => Nat)
              (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkSt (Nat.add r (nat_lit 1)) S len j)
                (eqCheck T L (Nat.xor (maskN n) (Nat.lor (Nat.land S (maskN n)) (nat_lit 1)))))
              (sN (dBits DL ch) (fun DB => sN (Nat.lor S DB) (fun S' =>
                Bool.rec (motive := fun _ => Nat) (nat_lit 0)
                  (mkSt (Nat.add r (nat_lit 1)) S' (Nat.add len (fw ch (nat_lit 16) (nat_lit 1))) (Nat.add j (nat_lit 1)))
                  (andB (Nat.blt (nat_lit 0) DB) (andB (Nat.beq (Nat.land DB S) (nat_lit 0))
                    (andB (Nat.beq (Nat.land DB (Nat.sub (maskN n) (nat_lit 1))) DB)
                      (andB (eqCheck T L (Nat.xor (maskN n) (Nat.lor (Nat.land S' (maskN n)) (nat_lit 1))))
                        (andB (ltCheck T L DB)
                          (appendOk TD len (fw ch (nat_lit 16) (nat_lit 1)) S' DB n)))))))))
              (Nat.beq (fw ch (nat_lit 16) (nat_lit 0)) (Nat.add r (nat_lit 1))))))
        (andB (Nat.blt r len) (andB (notB (Nat.beq S (maskN n)))
          (Nat.beq (Nat.land st (nat_lit 65535)) r)))))))
    (Nat.blt (nat_lit 0) st)

@[expose] noncomputable def partOk (FS FI FT FM : Nat → Nat) (n TD CHL DL r0 cnt STa STb : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) STb)
    (sB (iterN cnt (fun i st => roundStep FS FI FT FM n TD CHL DL (Nat.add r0 i) st) STa) (fun st =>
      Nat.beq st STb))

@[expose] noncomputable def finalOk (n R SF STz : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) STz) (andB (Nat.beq (Nat.land STz (nat_lit 65535)) R)
    (andB (Nat.beq (stS STz) SF) (orB (Nat.beq (stL STz) R) (Nat.beq (stS STz) (maskN n)))))

@[expose] noncomputable def withCall (NW TA MB : Nat) (k : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Bool) :
    Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) (arrNW NW) (fun FS =>
    fsplit (nat_lit 1024) (nat_lit 6) (arrInvNW NW) (fun FI =>
      fsplit (nat_lit 1024) (nat_lit 6) TA (fun FT =>
        sB REP (fun R => fsplit (nat_lit 65536) (nat_lit 8) (applyNW NW R MB) (fun FM => k FS FI FT FM)))))

@[expose] noncomputable def rangeOk (FS : Nat → Nat) (n : Nat) : Bool :=
  allLt n (fun p => Nat.blt (ent FS p) n)

@[expose] noncomputable def partCall (n TA MB NW TD CHL DL r0 cnt STa STb : Nat) : Bool :=
  withCall NW TA MB (fun FS FI FT FM => partOk FS FI FT FM n TD CHL DL r0 cnt STa STb)

@[expose] noncomputable def rootIn (n TA NW TD f ST0 : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) (arrNW NW) (fun FS => fsplit (nat_lit 1024) (nat_lit 6) TA (fun FT =>
    andB (andB (andB (Nat.blt (nat_lit 0) f) (Nat.blt f n)) (rangeOk FS n))
      (andB (allLt n (fun p => sB (ent FS p) (fun v => Nat.beq (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
          (Nat.beq (ent FT v) v)) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.blt p f)))))
        (sB (Nat.lor (nat_lit 1) (Nat.shiftLeft (nat_lit 1) f)) (fun Sin =>
          andB (initOk TD (nat_lit 2) Sin n) (Nat.beq ST0 (mkSt (nat_lit 0) Sin (nat_lit 2) (nat_lit 0))))))))

@[expose] noncomputable def sameCell (S x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Nat.beq (Nat.land (Nat.shiftRight S (Nat.add x (nat_lit 1))) (maskN (Nat.sub y x))) (nat_lit 0))
    (Nat.beq (Nat.land (Nat.shiftRight S (Nat.add y (nat_lit 1))) (maskN (Nat.sub x y))) (nat_lit 0))
    (Nat.blt y x)

@[expose] noncomputable def splitStarts (SP n c e : Nat) : Nat :=
  Nat.lor (Nat.land SP (maskN c))
    (Nat.lor (Nat.shiftLeft (Nat.shiftRight SP e) c)
      (Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.sub n (Nat.sub e c)))
        (Nat.mul (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.sub n (Nat.sub e c)) (nat_lit 1)))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.blt (nat_lit 1) (Nat.sub e c))))))

@[expose] noncomputable def placeOk (SP n c e q p o : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.ble c o) (andB (Nat.blt o e) (notB (Nat.beq o q))))
        (Nat.beq o q) (Nat.beq p (Nat.sub n (Nat.sub e c))))
      (sameCell SP o (Nat.add p (Nat.sub e c))) (Nat.blt p (Nat.sub n (Nat.sub e c))))
    (sameCell SP o p) (Nat.blt p c)

@[expose] noncomputable def splitIn (n NWP SP v q c e m NW TD ST0 : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) (arrNW NWP) (fun GS =>
    fsplit (nat_lit 1024) (nat_lit 6) (arrInvNW NWP) (fun GI =>
      fsplit (nat_lit 1024) (nat_lit 6) (arrNW NW) (fun FS =>
        andB (andB (Nat.beq (ent GS q) v) (andB (isCell SP n c e) (andB (Nat.ble c q) (Nat.blt q e))))
          (andB (andB (rangeOk FS n) (allLt n (fun p => placeOk SP n c e q p (ent GI (ent FS p)))))
            (sB (splitStarts SP n c e) (fun Sin =>
              andB (initOk TD m Sin n) (Nat.beq ST0 (mkSt (nat_lit 0) Sin m (nat_lit 0)))))))))

end CFSG.KLC.Fi22

end
