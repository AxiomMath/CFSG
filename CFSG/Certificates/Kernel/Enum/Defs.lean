module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def strictN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def foldBlk (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun l ih s => strictN (f (Nat.add b l) s) ih) len s

@[expose] noncomputable def foldN (n : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  (fun q => Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
      q (foldBlk (Nat.shiftLeft q (nat_lit 6)) f (Nat.land n (nat_lit 63)) s))
    (Nat.shiftRight n (nat_lit 6))

@[expose] noncomputable def allBlk (b : Nat) (f : Nat → Bool) (len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun l ih => bAnd(f (Nat.add b l), ih)) len

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  (fun q => bAnd(allBlk (Nat.shiftLeft q (nat_lit 6)) f (Nat.land n (nat_lit 63)),
      Nat.rec (motive := fun _ => Bool) true
        (fun h ih => bAnd(allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64), ih)) q))
    (Nat.shiftRight n (nat_lit 6))

@[expose] noncomputable def pg (w m p i : Nat) : Nat := fld(p, Nat.mul w i, m)

@[expose] noncomputable def clog (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ ih => nIf(Nat.blt (Nat.shiftLeft (nat_lit 1) ih) n, Nat.succ ih, ih)) (nat_lit 24)

@[expose] noncomputable def pmkT (n w : Nat) (f : Nat → Nat) (d lo : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => nIf(Nat.blt lo n, f lo, nat_lit 0))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))) (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))))
    d lo

@[expose] noncomputable def pmk (n w : Nat) (f : Nat → Nat) : Nat :=
  strictN (clog n) (fun d => pmkT n w f d (nat_lit 0))

@[expose] noncomputable def pidn (n w : Nat) : Nat := pmk n w (fun i => i)

@[expose] noncomputable def pmkH (w m p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => fld(p, Nat.mul w fld(q, Nat.mul w lo, m), m))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))) (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))))

@[expose] noncomputable def pmkH8 (w m p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun lo => Nat.lor
      (Nat.lor
        (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w lo, m), m)
          (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 1)), m), m) w))
        (Nat.shiftLeft
          (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 2)), m), m)
            (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 3)), m), m) w))
          (Nat.mul w (nat_lit 2))))
      (Nat.shiftLeft
        (Nat.lor
          (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 4)), m), m)
            (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 5)), m), m) w))
          (Nat.shiftLeft
            (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 6)), m), m)
              (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 7)), m), m) w))
            (Nat.mul w (nat_lit 2))))
        (Nat.mul w (nat_lit 4))))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 8) d))) (Nat.mul w (Nat.shiftLeft (nat_lit 8) d))))

@[expose] noncomputable def pcomp (n w m p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkH w m p q b lo, pmkH8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))
    (nat_lit 32) (nat_lit 0) n

@[expose] noncomputable def eq2 (n w m r p q : Nat) : Bool :=
  allN n (fun i => Nat.beq (pg w m r i) (pg w m p (pg w m q i)))

@[expose] noncomputable def eq3 (n w m r p q s : Nat) : Bool :=
  allN n (fun i => Nat.beq (pg w m r i) (pg w m p (pg w m q (pg w m s i))))

@[expose] noncomputable def eq22 (n w m p q r s : Nat) : Bool :=
  allN n (fun i => Nat.beq (pg w m p (pg w m q i)) (pg w m r (pg w m s i)))

@[expose] noncomputable def invoOK (n w m nw x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x nw) (nat_lit 0),
    allN n (fun i => strictB (pg w m x i) (fun v => bAnd(Nat.blt v n, Nat.beq (pg w m x v) i))))

@[expose] noncomputable def permOK (n w m nw p q : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight p nw) (nat_lit 0), bAnd(Nat.beq (Nat.shiftRight q nw) (nat_lit 0),
    allN n (fun i => strictB (pg w m p i) (fun v => bAnd(Nat.blt v n, Nat.beq (pg w m q v) i)))))

@[expose] noncomputable def lt (w m X Y Xi Yi c q : Nat) : Nat :=
  pg w m (nIf(Nat.beq c (nat_lit 0), X, nIf(Nat.beq c (nat_lit 1), Y,
    nIf(Nat.beq c (nat_lit 2), Xi, Yi)))) q

@[expose] noncomputable def wpt (w m X Y Xi Yi W len q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun k ih q => strictN (lt w m X Y Xi Yi fld(W, Nat.shiftLeft k (nat_lit 1), nat_lit 3) q) ih)
    len q

@[expose] noncomputable def fpow (f : Nat → Nat) (o q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q) (fun _ ih q => strictN (f q) ih) o q

@[expose] noncomputable def cyc (f : Nat → Nat) (p o : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun k ih q => strictN (f q) (fun q' => nIf(Nat.beq q' p, Nat.sub o k, ih q'))) o p

@[expose] noncomputable def ordAll (n : Nat) (f : Nat → Nat) (o : Nat) : Nat :=
  foldN n (fun p s => nIf(Nat.beq s (nat_lit 0), nat_lit 0, strictN (cyc f p o) (fun r =>
    nIf(Nat.beq r (nat_lit 0), nat_lit 0, Nat.div (Nat.mul s r) (Nat.gcd s r))))) (nat_lit 1)

@[expose] noncomputable def ordIs (n : Nat) (f : Nat → Nat) (o : Nat) : Bool :=
  Nat.beq (ordAll n f o) o

@[expose] noncomputable def wl (W k : Nat) : Nat := fld(W, Nat.shiftLeft k (nat_lit 1), nat_lit 3)

@[expose] noncomputable def wperm (n w m a b ai bi W len : Nat) : Nat :=
  pmk n w (fun p => foldN len (fun k q => lt w m a b ai bi (wl W k) q) p)

@[expose] noncomputable def dW (d : Nat) : Nat := Nat.land d (nat_lit 18446744073709551615)

@[expose] noncomputable def dL (d : Nat) : Nat := fld(d, nat_lit 64, nat_lit 255)

@[expose] noncomputable def dO (d : Nat) : Nat := fld(d, nat_lit 72, nat_lit 255)

@[expose] noncomputable def wordOrdOK (n w m X Y Xi Yi d : Nat) : Bool :=
  ordIs n (wpt w m X Y Xi Yi (dW d) (dL d)) (dO d)

@[expose] noncomputable def wordsOK (n w m X Y Xi Yi : Nat) (ws : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => bAnd(wordOrdOK n w m X Y Xi Yi d, ih)) ws

@[expose] noncomputable def patchT (T : Nat → Nat) (L leaf k : Nat) : Nat :=
  nIf(Nat.beq k L, leaf, T k)

@[expose] noncomputable def rget (T : Nat → Nat) (sh lm rb rm i : Nat) : Nat :=
  strictN (Nat.shiftRight i sh) (fun b => fld(T b, Nat.mul rb (Nat.land i lm), rm))

@[expose] noncomputable def rperm (T : Nat → Nat) (sh lm rb rm pm j : Nat) : Nat :=
  Nat.land (rget T sh lm rb rm j) pm

@[expose] noncomputable def lChk (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im nL a ai b bi i : Nat) :
    Bool :=
  strictB (rget T sh lm rb rm i) (fun r =>
    strictB (Nat.land r pm) (fun x =>
      strictB fld(r, nw, im) (fun ca => strictB fld(r, Nat.add nw iw, im) (fun cb =>
        bAnd(invoOK n w m nw x, bAnd(Nat.blt ca nL, bAnd(Nat.blt cb nL,
          bAnd(eq3 n w m (rperm T sh lm rb rm pm ca) a x ai,
            eq3 n w m (rperm T sh lm rb rm pm cb) b x bi))))))))

@[expose] noncomputable def lRange (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im nL a ai b bi lo cnt : Nat) :
    Bool :=
  allN cnt (fun k => lChk T sh lm rb rm n w m nw pm iw im nL a ai b bi (Nat.add lo k))

@[expose] noncomputable def sClos (T : Nat → Nat) (sh lm rb rm n w m pm iw im nS : Nat)
    (G : Nat → Nat) (k r e oR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
    strictB fld(r, Nat.add oR (Nat.mul iw j), im) (fun Rj =>
      bAnd(Nat.blt Rj nS, eq2 n w m (rperm T sh lm rb rm pm Rj) e (G j))),
    ih)) k

@[expose] noncomputable def sChk (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im nS idn : Nat)
    (G : Nat → Nat) (k : Nat) (fInv : Bool) (LT : Nat → Nat) (lsh llm lrb lrm nL : Nat) (fWit : Bool)
    (ob : Nat) (C : Nat → Nat) (nC : Nat) (Y : Nat → Nat) (nK i : Nat) : Bool :=
  strictB (rget T sh lm rb rm i) (fun r =>
  strictB (Nat.land r pm) (fun e =>
  strictB fld(r, nw, im) (fun par =>
  strictB fld(r, Nat.add nw iw, nat_lit 15) (fun lab =>
  strictB fld(r, Nat.add nw (Nat.add iw (nat_lit 4)), nat_lit 255) (fun dep =>
  strictB (Nat.add nw (Nat.add iw (nat_lit 12))) (fun oR =>
  bAnd(
    bIf(Nat.beq i (nat_lit 0), true, Nat.blt (rperm T sh lm rb rm pm (Nat.sub i (nat_lit 1))) e),
    bAnd(
    bIf(Nat.beq dep (nat_lit 0), Nat.beq e idn,
      bAnd(Nat.blt par nS, bAnd(Nat.blt lab k,
        bAnd(Nat.beq fld(rget T sh lm rb rm par, Nat.add nw (Nat.add iw (nat_lit 4)), nat_lit 255)
            (Nat.sub dep (nat_lit 1)),
          eq2 n w m e (rperm T sh lm rb rm pm par) (G lab))))),
    bAnd(
    sClos T sh lm rb rm n w m pm iw im nS G k r e oR,
    bAnd(
    bIf(fInv, bIf(bAnd(eq2 n w m idn e e, bIf(Nat.beq e idn, false, true)),
      strictB fld(r, Nat.add oR (Nat.mul iw k), im) (fun ix =>
        bAnd(Nat.blt ix nL, Nat.beq (rperm LT lsh llm lrb lrm pm ix) e)), true), true),
    bIf(fWit, bIf(ordIs n (pg w m e) ob,
      strictB fld(r, Nat.add oR (Nat.mul iw (Nat.succ k)), im) (fun t =>
      strictB fld(r, Nat.add oR (Nat.mul iw (Nat.add k (nat_lit 2))), nat_lit 255) (fun wi =>
      strictB fld(r, Nat.add (Nat.add oR (Nat.mul iw (Nat.add k (nat_lit 2)))) (nat_lit 8),
          nat_lit 15) (fun K =>
        bAnd(Nat.blt t nS, bAnd(Nat.blt wi nC, bAnd(Nat.blt K nK,
          strictB (pcomp n w m (C wi) (rperm T sh lm rb rm pm t)) (fun g =>
            eq22 n w m g e (Y K) g))))))), true), true)))))))))))

@[expose] noncomputable def sRange (T : Nat → Nat) (sh lm rb rm n w m nw pm iw im nS idn : Nat)
    (G : Nat → Nat) (k : Nat) (fInv : Bool) (LT : Nat → Nat) (lsh llm lrb lrm nL : Nat) (fWit : Bool)
    (ob : Nat) (C : Nat → Nat) (nC : Nat) (Y : Nat → Nat) (nK lo cnt : Nat) : Bool :=
  allN cnt (fun j => sChk T sh lm rb rm n w m nw pm iw im nS idn G k fInv LT lsh llm lrb lrm nL fWit
    ob C nC Y nK (Nat.add lo j))

@[expose] noncomputable def sumL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.add x ih) l

@[expose] noncomputable def sylowOK (N p e nS : Nat) : Bool :=
  bAnd(Nat.beq nS (Nat.pow p e), bAnd(Nat.beq (Nat.mod N nS) (nat_lit 0),
    bIf(Nat.beq (Nat.mod (Nat.div N nS) p) (nat_lit 0), false, true)))

@[expose] noncomputable def commOK (n w m z y : Nat) : Bool := eq22 n w m z y y z

@[expose] noncomputable def pairOK (n w m x y yi : Nat) (ws tp : List Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true (fun d _ ih => bAnd(
      List.rec (motive := fun _ => Bool) true (fun p _ ih2 => bAnd(
        Nat.beq (fpow (wpt w m x y x yi (dW d) (dL d)) (dO d) p) p, ih2)) tp, ih)) ws,
    wordsOK n w m x y x yi ws)

@[expose] noncomputable def scanCnt (T : Nat → Nat) (sh lm rb rm n w m pm y yi : Nat)
    (ws tp : List Nat) (lo cnt : Nat) : Nat :=
  foldN cnt (fun j s => nIf(pairOK n w m (rperm T sh lm rb rm pm (Nat.add lo j)) y yi ws tp,
    Nat.succ s, s)) (nat_lit 0)

end CFSG.KC.Enum

end
