module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def mrow (d rm M i : Nat) : Nat := fld(M, Nat.mul d i, rm)

@[expose] noncomputable def mmul (d rm C M N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight M j) C) (mrow d rm N j))) d

@[expose] noncomputable def par32 (x : Nat) : Nat :=
  strictN (Nat.xor x (Nat.shiftRight x (nat_lit 16))) (fun x =>
  strictN (Nat.xor x (Nat.shiftRight x (nat_lit 8))) (fun x =>
  strictN (Nat.xor x (Nat.shiftRight x (nat_lit 4))) (fun x =>
  strictN (Nat.xor x (Nat.shiftRight x (nat_lit 2))) (fun x =>
    Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 1))) (nat_lit 1)))))

@[expose] noncomputable def mvec (d rm M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun i ih acc => strictN (Nat.lor acc (Nat.shiftLeft (par32 (Nat.land (mrow d rm M i) v)) i)) ih)
    d (nat_lit 0)

@[expose] noncomputable def liftOK (d rm n w m M P V : Nat) : Bool :=
  allN n (fun i => Nat.beq (mvec d rm M (mrow d rm V i)) (mrow d rm V (pg w m P i)))

@[expose] noncomputable def cChk (T : Nat → Nat) (sh lm rb rm' : Nat) (d rm C mm iw im nO X A Ai B Bi i : Nat) :
    Bool :=
  strictB (rget T sh lm rb rm' i) (fun r =>
  strictB (Nat.land r mm) (fun M =>
  strictB (Nat.mul d d) (fun dd =>
  strictB fld(r, dd, im) (fun par =>
  strictB fld(r, Nat.add dd iw, nat_lit 1) (fun lab =>
  strictB fld(r, Nat.add dd (Nat.succ iw), nat_lit 255) (fun dep =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (Nat.land (rget T sh lm rb rm' (Nat.sub i (nat_lit 1))) mm) M),
  bIf(Nat.beq dep (nat_lit 0), Nat.beq M X,
    bAnd(Nat.blt par nO, strictB (rget T sh lm rb rm' par) (fun rp =>
      bAnd(Nat.beq fld(rp, Nat.add dd (Nat.succ iw), nat_lit 255) (Nat.sub dep (nat_lit 1)),
        Nat.beq M (mmul d rm C (nIf(Nat.beq lab (nat_lit 0), A, B))
          (mmul d rm C (Nat.land rp mm) (nIf(Nat.beq lab (nat_lit 0), Ai, Bi)))))))))))))))

@[expose] noncomputable def cRange (T : Nat → Nat) (sh lm rb rm' : Nat) (d rm C mm iw im nO X A Ai B Bi lo cnt : Nat) :
    Bool :=
  allN cnt (fun k => cChk T sh lm rb rm' d rm C mm iw im nO X A Ai B Bi (Nat.add lo k))

@[expose] noncomputable def mSChk (T : Nat → Nat) (sh lm rb rm' : Nat) (d rm C mm iw im nS I : Nat)
    (G : Nat → Nat) (k i : Nat) : Bool :=
  strictB (rget T sh lm rb rm' i) (fun r =>
  strictB (Nat.land r mm) (fun M =>
  strictB (Nat.mul d d) (fun dd =>
  strictB fld(r, dd, im) (fun par =>
  strictB fld(r, Nat.add dd iw, nat_lit 15) (fun lab =>
  strictB fld(r, Nat.add dd (Nat.add iw (nat_lit 4)), nat_lit 255) (fun dep =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (Nat.land (rget T sh lm rb rm' (Nat.sub i (nat_lit 1))) mm) M),
  bAnd(bIf(Nat.beq dep (nat_lit 0), Nat.beq M I,
    bAnd(Nat.blt par nS, bAnd(Nat.blt lab k, strictB (rget T sh lm rb rm' par) (fun rp =>
      bAnd(Nat.beq fld(rp, Nat.add dd (Nat.add iw (nat_lit 4)), nat_lit 255) (Nat.sub dep (nat_lit 1)),
        Nat.beq M (mmul d rm C (Nat.land rp mm) (G lab))))))),
    Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
      strictB fld(r, Nat.add (Nat.add dd (Nat.add iw (nat_lit 12))) (Nat.mul iw j), im) (fun Rj =>
        bAnd(Nat.blt Rj nS, Nat.beq (Nat.land (rget T sh lm rb rm' Rj) mm) (mmul d rm C M (G j)))), ih)) k))))))))

@[expose] noncomputable def mSRange (T : Nat → Nat) (sh lm rb rm' : Nat) (d rm C mm iw im nS I : Nat)
    (G : Nat → Nat) (k lo cnt : Nat) : Bool :=
  allN cnt (fun j => mSChk T sh lm rb rm' d rm C mm iw im nS I G k (Nat.add lo j))

@[expose] noncomputable def mAt (T : Nat → Nat) (sh lm rb rm' mm j : Nat) : Nat :=
  Nat.land (rget T sh lm rb rm' j) mm

@[expose] noncomputable def mNotIn (T : Nat → Nat) (sh lm rb rm' mm n X j : Nat) : Bool :=
  bIf(Nat.beq j n, Nat.blt X (mAt T sh lm rb rm' mm (nat_lit 0)),
    bIf(Nat.beq j (Nat.succ n), Nat.blt (mAt T sh lm rb rm' mm (Nat.sub n (nat_lit 1))) X,
      bAnd(Nat.blt (Nat.succ j) n, bAnd(Nat.blt (mAt T sh lm rb rm' mm j) X,
        Nat.blt X (mAt T sh lm rb rm' mm (Nat.succ j))))))

@[expose] noncomputable def mpow (d rm C I M p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun _ ih acc => strictN (mmul d rm C acc M) ih) p I

@[expose] noncomputable def mword (d rm C I : Nat) (F : Nat → Nat) (W len cw cm : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun k ih acc => strictN (mmul d rm C (F fld(W, Nat.mul cw k, cm)) acc) ih) len I

@[expose] noncomputable def mCountOrd (T : Nat → Nat) (sh lm rb rm' mm d rm C I p n : Nat) : Nat :=
  foldN n (fun j s => strictN (mAt T sh lm rb rm' mm j) (fun M =>
    nIf(bAnd(Nat.beq (mpow d rm C I M p) I, bIf(Nat.beq M I, false, true)), Nat.succ s, s))) (nat_lit 0)

@[expose] noncomputable def fusOK (T : Nat → Nat) (sh lm rb rm' : Nat) (DT : Nat → Nat) (dsh dlm drb drm' : Nat)
    (mm d rm C I p n : Nat) (R : Nat → Nat) (wl : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih prev => strictB fld(e, nat_lit 0, nat_lit 16777215) (fun ei =>
      bAnd(Nat.ble prev ei, bAnd(Nat.blt ei n,
        strictB (mAt T sh lm rb rm' mm ei) (fun M =>
        strictB (mAt DT dsh dlm drb drm' mm fld(e, nat_lit 24, nat_lit 16777215)) (fun H =>
          bAnd(Nat.beq (mpow d rm C I M p) I, bAnd(bIf(Nat.beq M I, false, true),
            bAnd(bIf(Nat.beq H (nat_lit 0), false, true),
            bAnd(Nat.beq (mmul d rm C H M) (mmul d rm C (R fld(e, nat_lit 48, nat_lit 255)) H),
              ih (Nat.succ ei))))))))))) wl (nat_lit 0)

@[expose] noncomputable def mLChk (T : Nat → Nat) (sh lm rb rm' : Nat) (d rm C mm iw im nS I Z : Nat)
    (G V : Nat → Nat) (k i : Nat) : Bool :=
  bAnd(mSChk T sh lm rb rm' d rm C mm iw im nS I G k i,
  strictB (rget T sh lm rb rm' i) (fun r =>
  strictB (Nat.land r mm) (fun M =>
  strictB (Nat.add (Nat.mul d d) (Nat.add iw (nat_lit 12))) (fun oR =>
  strictB fld(r, Nat.add oR (Nat.mul iw k), nat_lit 31) (fun lb =>
  bAnd(bIf(Nat.beq fld(r, Nat.add (Nat.mul d d) (Nat.add iw (nat_lit 4)), nat_lit 255) (nat_lit 0),
      Nat.beq lb (nat_lit 0),
      strictB (rget T sh lm rb rm' fld(r, Nat.mul d d, im)) (fun rp =>
        Nat.beq lb (Nat.xor fld(rp, Nat.add oR (Nat.mul iw k), nat_lit 31)
          (V fld(r, Nat.add (Nat.mul d d) iw, nat_lit 15))))),
  bAnd(Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
      Nat.beq fld(rget T sh lm rb rm' fld(r, Nat.add oR (Nat.mul iw j), im), Nat.add oR (Nat.mul iw k), nat_lit 31)
        (Nat.xor lb (V j)), ih)) k,
    bIf(bIf(Nat.beq M I, true, Nat.beq M Z), true,
      strictB (G fld(r, Nat.add (Nat.add oR (Nat.mul iw k)) (nat_lit 5), nat_lit 15)) (fun g =>
        bIf(Nat.beq (mmul d rm C M g) (mmul d rm C g M), false, true))))))))))

@[expose] noncomputable def mLRange (T : Nat → Nat) (sh lm rb rm' : Nat) (d rm C mm iw im nS I Z : Nat)
    (G V : Nat → Nat) (k lo cnt : Nat) : Bool :=
  allN cnt (fun j => mLChk T sh lm rb rm' d rm C mm iw im nS I Z G V k (Nat.add lo j))

@[expose] noncomputable def ord2 (d rm C I Y M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 6)
    (fun _ ih e M => nIf(bIf(Nat.beq M I, true, Nat.beq M Y), e,
      strictN (mmul d rm C M M) (fun M2 => ih (Nat.succ e) M2)))
    (nat_lit 6) (nat_lit 0) M

@[expose] noncomputable def profChunk (T : Nat → Nat) (sh lm rb rm' : Nat) (d rm C mm iw I Z k lo cnt : Nat) : Nat :=
  foldN cnt (fun j s => strictN (rget T sh lm rb rm' (Nat.add lo j)) (fun r =>
    strictN (Nat.land r mm) (fun M =>
    strictN (Nat.mul (nat_lit 12) fld(r, Nat.add (Nat.add (Nat.mul d d) (Nat.add iw (nat_lit 12))) (Nat.mul iw k), nat_lit 31)) (fun c =>
      Nat.add (Nat.add s (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 19) (Nat.add c (ord2 d rm C I Z M)))))
        (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 19) (Nat.add (Nat.add c (nat_lit 6)) (ord2 d rm C I I M))))))))
    (nat_lit 0)

@[expose] noncomputable def prof (Pr v : Nat) : Nat :=
  fld(Pr, Nat.mul (nat_lit 228) v, nat_lit 431359146674410236714672241392314090778194310760649159697657763987455)

@[expose] noncomputable def uniqOK (Pr : Nat) (U : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ ih => bAnd(
    allN (nat_lit 32) (fun v => bIf(bIf(Nat.beq v (nat_lit 0), true, Nat.beq v u), true,
      bIf(Nat.beq (prof Pr v) (prof Pr u), false, true))), ih)) U

@[expose] noncomputable def spanOK (U : List Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat) (nat_lit 1) (fun u _ ih =>
    foldN (nat_lit 32) (fun v s => nIf(Nat.blt (nat_lit 0) (Nat.land ih (Nat.shiftLeft (nat_lit 1) v)),
      Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.xor v u)), s)) ih) U) (nat_lit 4294967295)

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

end CFSG.KC.Enum

end
