module

public import CFSG.Certificates.Kernel.Enum.DefsM

public section

namespace CFSG.KC.Local

open CFSG.KC.Enum

@[expose] noncomputable def pmkL (w m p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => fld(p, Nat.mul w fld(q, Nat.mul w lo, m), m))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))) (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))))

@[expose] noncomputable def pmkL8 (w m p q : Nat) : Nat → Nat → Nat :=
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

@[expose] noncomputable def pcompL (n w m p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkL w m p q b lo, pmkL8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))
    (nat_lit 32) (nat_lit 0) n

@[expose] noncomputable def foldB (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun l ih s => strictN (f (Nat.add b l) s) ih) len s

@[expose] noncomputable def foldL (n : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  (fun q => Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldB (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
      q (foldB (Nat.shiftLeft q (nat_lit 6)) f (Nat.land n (nat_lit 63)) s))
    (Nat.shiftRight n (nat_lit 6))

@[expose] noncomputable def allB (b : Nat) (f : Nat → Bool) (len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun l ih => bAnd(f (Nat.add b l), ih)) len

@[expose] noncomputable def allL (n : Nat) (f : Nat → Bool) : Bool :=
  (fun q => bAnd(allB (Nat.shiftLeft q (nat_lit 6)) f (Nat.land n (nat_lit 63)),
      Nat.rec (motive := fun _ => Bool) true
        (fun h ih => bAnd(allB (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64), ih)) q))
    (Nat.shiftRight n (nat_lit 6))

@[expose] noncomputable def rgetL (T : Nat → Nat) (sh lm rb rm i : Nat) : Nat :=
  strictN (Nat.shiftRight i sh) (fun b => fld(T b, Nat.mul rb (Nat.land i lm), rm))

@[expose] noncomputable def pop64 (x : Nat) : Nat :=
  (fun a => (fun b => (fun c =>
      Nat.shiftRight (Nat.land (Nat.mul c (nat_lit 72340172838076673)) (nat_lit 18446744073709551615)) (nat_lit 56))
    (Nat.land (Nat.add b (Nat.shiftRight b (nat_lit 4))) (nat_lit 1085102592571150095)))
    (Nat.add (Nat.land a (nat_lit 3689348814741910323)) (Nat.land (Nat.shiftRight a (nat_lit 2)) (nat_lit 3689348814741910323))))
    (Nat.sub x (Nat.land (Nat.shiftRight x (nat_lit 1)) (nat_lit 6148914691236517205)))

@[expose] noncomputable def wordFold (f : Nat → Nat → Nat) (base : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih w s => nIf(Nat.beq w (nat_lit 0), s,
      (fun low => strictN (f (Nat.add base (pop64 (Nat.sub low (nat_lit 1)))) s) (fun s2 => ih (Nat.xor w low) s2))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1))))))
    (nat_lit 64)

@[expose] noncomputable def foldBits (n : Nat) (f : Nat → Nat → Nat) (M s : Nat) : Nat :=
  (fun M' => Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih j s => strictN (wordFold f (Nat.shiftLeft j (nat_lit 6))
        (Nat.land (Nat.shiftRight M' (Nat.shiftLeft j (nat_lit 6))) (nat_lit 18446744073709551615)) s)
      (fun s2 => ih (Nat.succ j) s2))
    (Nat.shiftRight (Nat.add n (nat_lit 63)) (nat_lit 6)) (nat_lit 0) s)
  (Nat.land M (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))

@[expose] noncomputable def wordAll (f : Nat → Bool) (base : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih w => bIf(Nat.beq w (nat_lit 0), true,
      (fun low => bAnd(f (Nat.add base (pop64 (Nat.sub low (nat_lit 1)))), ih (Nat.xor w low)))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1))))))
    (nat_lit 64)

@[expose] noncomputable def allBits (n : Nat) (f : Nat → Bool) (M : Nat) : Bool :=
  (fun M' => Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih j => bAnd(wordAll f (Nat.shiftLeft j (nat_lit 6))
        (Nat.land (Nat.shiftRight M' (Nat.shiftLeft j (nat_lit 6))) (nat_lit 18446744073709551615)),
      ih (Nat.succ j)))
    (Nat.shiftRight (Nat.add n (nat_lit 63)) (nat_lit 6)) (nat_lit 0))
  (Nat.land M (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))

@[expose] noncomputable def mulK (K a b c x y : Nat) : Nat :=
  nIf(Nat.beq K (nat_lit 0), pcompL a b c x y, mmul a b c x y)

@[expose] noncomputable def powK (K a b c idn x e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (mulK K a b c acc acc) (fun a2 =>
      strictN (nIf(Nat.blt (nat_lit 0) (Nat.land e (Nat.shiftLeft (nat_lit 1) j)),
        mulK K a b c a2 x, a2)) ih)) nb idn

@[expose] noncomputable def nbits (e : Nat) : Nat :=
  nIf(Nat.beq e (nat_lit 0), nat_lit 0, Nat.succ
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k ih => strictN ih (fun acc => strictN (Nat.add acc (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 6) k)))
        (fun t => nIf(Nat.beq (Nat.shiftRight e t) (nat_lit 0), acc, t)))) (nat_lit 7)))

@[expose] noncomputable def powE (K a b c idn x e : Nat) : Nat :=
  strictN (nbits e) (fun nb => powK K a b c idn x e nb)

@[expose] noncomputable def ordOK (K a b c idn x o : Nat) (ps : List Nat) : Bool :=
  bAnd(Nat.beq (powE K a b c idn x o) idn,
    List.rec (motive := fun _ => Bool) true (fun p _ ih =>
      bAnd(bIf(Nat.beq (powE K a b c idn x (Nat.div o p)) idn, false, true), ih)) ps)

@[expose] noncomputable def commK (K a b c x y : Nat) : Bool :=
  Nat.beq (mulK K a b c x y) (mulK K a b c y x)

@[expose] noncomputable def commAll (K a b c x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(commK K a b c x y, ih)) l

@[expose] noncomputable def hd (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l

@[expose] noncomputable def tl (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) l

@[expose] noncomputable def lnth (l : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => nIf(Nat.beq j (nat_lit 0), x, ih (Nat.sub j (nat_lit 1)))) l j

@[expose] noncomputable def llen (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def conjPairs (K a b c x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool → Nat → Bool) (fun _ _ => true)
    (fun q _ ih second p => bIf(second, bAnd(Nat.beq (mulK K a b c x p) (mulK K a b c q x), ih false q),
      ih true q)) l false (nat_lit 0)

@[expose] noncomputable def anyPow (K a b c idn x : Nat) (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih =>
    bIf(Nat.beq (powE K a b c idn x p) idn, true, ih)) ps

@[expose] noncomputable def predK (code K a b c idn x : Nat) (prm : List Nat) : Bool :=
    bIf(Nat.beq code (nat_lit 0), true,
    bIf(Nat.beq code (nat_lit 1),
      bAnd(bIf(Nat.beq x idn, false, true), Nat.beq (mulK K a b c x x) idn),
    bIf(Nat.beq code (nat_lit 2), ordOK K a b c idn x (hd prm) (tl prm),
    bIf(Nat.beq code (nat_lit 3), strictB (mulK K a b c x x) (fun x2 =>
        bAnd(bIf(Nat.beq x2 idn, false, true), Nat.beq (mulK K a b c x2 x2) idn)),
    bIf(Nat.beq code (nat_lit 4), bAnd(bIf(Nat.beq x idn, false, true), anyPow K a b c idn x prm),
    bIf(Nat.beq code (nat_lit 5), commAll K a b c x prm,
    bIf(Nat.beq code (nat_lit 6),
      bAnd(bIf(Nat.beq x idn, false, true), Nat.beq (powE K a b c idn x (hd prm)) idn),
    bIf(Nat.beq code (nat_lit 7), conjPairs K a b c x prm,
    bIf(Nat.beq code (nat_lit 8), strictB (mulK K a b c x (hd prm)) (fun y =>
        bAnd(bIf(Nat.beq y idn, false, true), Nat.beq (mulK K a b c y y) idn)),
      false)))))))))

@[expose] noncomputable def elt (T : Nat → Nat) (sh lm rb rm em i : Nat) : Nat :=
  Nat.land (rgetL T sh lm rb rm i) em

@[expose] noncomputable def glClos (T : Nat → Nat) (sh lm rb rm K a b c em iw im nS r e oR : Nat)
    (G : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih j => bAnd(
      strictB fld(r, Nat.add oR (Nat.mul iw j), im) (fun Rj =>
        bAnd(Nat.blt Rj nS, Nat.beq (elt T sh lm rb rm em Rj) (mulK K a b c e g))),
      ih (Nat.succ j))) G

@[expose] noncomputable def glChk (T : Nat → Nat) (sh lm rb rm K a b c eb em iw im dw dm : Nat)
    (G : List Nat) (k idn nS i : Nat) : Bool :=
  strictB (rgetL T sh lm rb rm i) (fun r =>
  strictB (Nat.land r em) (fun e =>
  strictB fld(r, eb, im) (fun par =>
  strictB fld(r, Nat.add eb iw, nat_lit 15) (fun lab =>
  strictB (Nat.add eb (Nat.add iw (nat_lit 4))) (fun od =>
  strictB fld(r, od, dm) (fun dep =>
  strictB (Nat.add od dw) (fun oR =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (elt T sh lm rb rm em (Nat.sub i (nat_lit 1))) e),
  bAnd(bIf(Nat.beq dep (nat_lit 0), Nat.beq e idn,
    bAnd(Nat.blt par nS, bAnd(Nat.blt lab k, strictB (rgetL T sh lm rb rm par) (fun rp =>
      bAnd(Nat.beq (Nat.succ fld(rp, od, dm)) dep,
        Nat.beq fld(rp, Nat.add oR (Nat.mul iw lab), im) i))))),
    glClos T sh lm rb rm K a b c em iw im nS r e oR G (nat_lit 0))))))))))

@[expose] noncomputable def glRange (T : Nat → Nat) (sh lm rb rm K a b c eb em iw im dw dm : Nat)
    (G : List Nat) (k idn nS lo cnt : Nat) : Bool :=
  allL cnt (fun j => glChk T sh lm rb rm K a b c eb em iw im dw dm G k idn nS (Nat.add lo j))

@[expose] noncomputable def memOK (T : Nat → Nat) (sh lm rb rm em n x j : Nat) : Bool :=
  bAnd(Nat.blt j n, Nat.beq (elt T sh lm rb rm em j) x)

@[expose] noncomputable def conjIn (T : Nat → Nat) (sh lm rb rm em n K a b c x h j : Nat) : Bool :=
  bAnd(Nat.blt j n, Nat.beq (mulK K a b c (elt T sh lm rb rm em j) x) (mulK K a b c x h))

@[expose] noncomputable def clConj (T : Nat → Nat) (sh lm rb rm K a b c em eb cm iw im nC r e cl oP : Nat)
    (H : List Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
    (fun h _ ih H2 j => bAnd(
      strictB fld(r, Nat.add oP (Nat.mul iw j), im) (fun Pj =>
        bAnd(Nat.blt Pj nC, strictB (rgetL T sh lm rb rm Pj) (fun rq =>
          bAnd(Nat.beq fld(rq, eb, cm) cl,
            Nat.beq (mulK K a b c (Nat.land rq em) (hd H2)) (mulK K a b c h e))))),
      ih (tl H2) (Nat.succ j))) H

@[expose] noncomputable def clChk (T : Nat → Nat) (sh lm rb rm K a b c idn eb em cw cm iw im dw dm : Nat)
    (H H2 : List Nat) (k nC ncl REP : Nat) (GT : Nat → Nat) (gsh glm grb grm nG code : Nat)
    (prm : List Nat) (i : Nat) : Bool :=
  strictB (rgetL T sh lm rb rm i) (fun r =>
  strictB (Nat.land r em) (fun e =>
  strictB fld(r, eb, cm) (fun cl =>
  strictB (Nat.add eb cw) (fun op =>
  strictB fld(r, op, im) (fun par =>
  strictB fld(r, Nat.add op iw, nat_lit 15) (fun lab =>
  strictB (Nat.add op (Nat.add iw (nat_lit 4))) (fun od =>
  strictB fld(r, od, dm) (fun dep =>
  strictB fld(r, Nat.add od dw, im) (fun gi =>
  strictB (Nat.add (Nat.add od dw) iw) (fun oP =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (elt T sh lm rb rm em (Nat.sub i (nat_lit 1))) e),
  bAnd(Nat.blt cl ncl,
  bAnd(bIf(Nat.beq dep (nat_lit 0), Nat.beq fld(REP, Nat.mul iw cl, im) i,
    bAnd(Nat.blt par nC, bAnd(Nat.blt lab k, strictB (rgetL T sh lm rb rm par) (fun rp =>
      bAnd(Nat.beq (Nat.succ fld(rp, od, dm)) dep, bAnd(Nat.beq fld(rp, eb, cm) cl,
        Nat.beq fld(rp, Nat.add oP (Nat.mul iw lab), im) i)))))),
  bAnd(bIf(Nat.beq nG (nat_lit 0), true, memOK GT gsh glm grb grm em nG e gi),
  bAnd(predK code K a b c idn e prm,
    clConj T sh lm rb rm K a b c em eb cm iw im nC r e cl oP H H2 (nat_lit 0))))))))))))))))

@[expose] noncomputable def clRange (T : Nat → Nat) (sh lm rb rm K a b c idn eb em cw cm iw im dw dm : Nat)
    (H H2 : List Nat) (k nC ncl REP : Nat) (GT : Nat → Nat) (gsh glm grb grm nG code : Nat)
    (prm : List Nat) (lo cnt : Nat) : Bool :=
  allL cnt (fun j => clChk T sh lm rb rm K a b c idn eb em cw cm iw im dw dm H H2 k nC ncl REP GT gsh glm grb
    grm nG code prm (Nat.add lo j))

@[expose] noncomputable def repOK (T : Nat → Nat) (sh lm rb rm eb cw cm iw im dm : Nat) (nC ncl REP : Nat) : Bool :=
  allL ncl (fun cl => strictB fld(REP, Nat.mul iw cl, im) (fun i =>
    bAnd(Nat.blt i nC, strictB (rgetL T sh lm rb rm i) (fun r =>
      bAnd(Nat.beq fld(r, eb, cm) cl, Nat.beq fld(r, Nat.add (Nat.add eb cw) (Nat.add iw (nat_lit 4)), dm)
        (nat_lit 0))))))

@[expose] noncomputable def clCount (T : Nat → Nat) (sh lm rb rm eb cm lo cnt : Nat) : Nat :=
  foldL cnt (fun j s => Nat.add s (Nat.shiftLeft (nat_lit 1)
    (Nat.mul (nat_lit 24) fld(rgetL T sh lm rb rm (Nat.add lo j), eb, cm)))) (nat_lit 0)

@[expose] noncomputable def cntRange (T : Nat → Nat) (sh lm rb rm em K a b c idn code : Nat)
    (prm : List Nat) (lo cnt : Nat) : Nat :=
  foldL cnt (fun j s => nIf(predK code K a b c idn (elt T sh lm rb rm em (Nat.add lo j)) prm,
    Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def clMemOK (T : Nat → Nat) (sh lm rb rm em eb cm n x cl j : Nat) : Bool :=
  bAnd(memOK T sh lm rb rm em n x j, Nat.beq fld(rgetL T sh lm rb rm j, eb, cm) cl)

@[expose] noncomputable def subsetOK (A : Nat → Nat) (ash alm arb arm : Nat) (B : Nat → Nat) (bsh blm brb brm : Nat)
    (em nB K a b c idn code : Nat) (prm : List Nat) (lo : Nat) (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih j => bAnd(strictB (elt A ash alm arb arm em j) (fun e =>
        bIf(predK code K a b c idn e prm, memOK B bsh blm brb brm em nB e p, true)), ih (Nat.succ j)))
    ps lo

@[expose] noncomputable def prodWitOK (C : Nat → Nat) (csh clm crb crm nC : Nat) (CT : Nat → Nat) (tsh tlm trb trm nT : Nat)
    (em K a b c idn x h hj yj o : Nat) (ps : List Nat) : Bool :=
  bAnd(memOK C csh clm crb crm em nC h hj,
  bAnd(conjIn CT tsh tlm trb trm em nT K a b c h x yj,
    ordOK K a b c idn (mulK K a b c x (elt CT tsh tlm trb trm em yj)) o ps))

@[expose] noncomputable def notInOK (T : Nat → Nat) (sh lm rb rm em n x j : Nat) : Bool :=
  bIf(Nat.beq j n, Nat.blt x (elt T sh lm rb rm em (nat_lit 0)),
    bIf(Nat.beq j (Nat.succ n), Nat.blt (elt T sh lm rb rm em (Nat.sub n (nat_lit 1))) x,
      bAnd(Nat.blt (Nat.succ j) n, bAnd(Nat.blt (elt T sh lm rb rm em j) x,
        Nat.blt x (elt T sh lm rb rm em (Nat.succ j))))))

@[expose] noncomputable def autoChk (GT : Nat → Nat) (sh lm rb rm em : Nat) (BT : Nat → Nat) (bsh blm brb brm : Nat)
    (K a b c iw im oR nS : Nat) (G2 : List Nat) (i : Nat) : Bool :=
  strictB (rgetL GT sh lm rb rm i) (fun r =>
  strictB (rgetL BT bsh blm brb brm i) (fun Bi =>
  bAnd(Nat.blt Bi nS, bAnd(Nat.beq (rgetL BT bsh blm brb brm Bi) i,
  strictB (elt GT sh lm rb rm em Bi) (fun f =>
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun g _ ih j => bAnd(
        Nat.beq (elt GT sh lm rb rm em (rgetL BT bsh blm brb brm fld(r, Nat.add oR (Nat.mul iw j), im)))
          (mulK K a b c f g), ih (Nat.succ j))) G2 (nat_lit 0))))))

@[expose] noncomputable def autoRange (GT : Nat → Nat) (sh lm rb rm em : Nat) (BT : Nat → Nat) (bsh blm brb brm : Nat)
    (K a b c iw im oR nS : Nat) (G2 : List Nat) (lo cnt : Nat) : Bool :=
  allL cnt (fun j => autoChk GT sh lm rb rm em BT bsh blm brb brm K a b c iw im oR nS G2 (Nat.add lo j))

@[expose] noncomputable def autoCnt (GT : Nat → Nat) (sh lm rb rm em : Nat) (BT : Nat → Nat) (bsh blm brb brm : Nat)
    (K a b c idn code lo cnt : Nat) : Nat :=
  foldL cnt (fun j s => strictN (Nat.add lo j) (fun i => strictN (rgetL BT bsh blm brb brm i) (fun Bi =>
    nIf(bIf(Nat.beq code (nat_lit 0),
        Nat.beq (mulK K a b c (elt GT sh lm rb rm em i) (elt GT sh lm rb rm em Bi)) idn,
        Nat.beq Bi i), Nat.succ s, s)))) (nat_lit 0)

@[expose] noncomputable def liftOK (GT : Nat → Nat) (sh lm rb rm em : Nat) (BT : Nat → Nat) (bsh blm brb brm : Nat)
    (n w m w2 m2 P e j : Nat) : Bool :=
  strictB (elt GT sh lm rb rm em j) (fun p =>
  strictB (elt GT sh lm rb rm em (rgetL BT bsh blm brb brm j)) (fun q =>
  bAnd(Nat.blt P (Nat.shiftLeft (nat_lit 1) (Nat.mul w2 (Nat.add n n))),
    allL n (fun i => bIf(Nat.beq e (nat_lit 0),
      bAnd(Nat.beq (pg w2 m2 P i) (pg w m p i), Nat.beq (pg w2 m2 P (Nat.add i n)) (Nat.add (pg w m q i) n)),
      bAnd(Nat.beq (pg w2 m2 P i) (Nat.add (pg w m q i) n), Nat.beq (pg w2 m2 P (Nat.add i n)) (pg w m p i)))))))

@[expose] noncomputable def invPairCnt (T : Nat → Nat) (sh lm rb rm em K a b c idn n lo cnt : Nat) : Nat :=
  foldL cnt (fun t s => strictN (elt T sh lm rb rm em (Nat.add lo t)) (fun u =>
    nIf(predK (nat_lit 1) K a b c idn u List.nil,
      foldL n (fun j s2 => strictN (elt T sh lm rb rm em j) (fun v =>
        nIf(bAnd(bIf(Nat.beq u v, false, true), bAnd(predK (nat_lit 1) K a b c idn v List.nil,
            commK K a b c u v)), Nat.succ s2, s2))) s, s))) (nat_lit 0)

@[expose] noncomputable def lexLt (n w m p q : Nat) : Bool :=
  strictB (foldL n (fun i s => nIf(Nat.beq (pg w m p i) (pg w m q i), s, i)) n) (fun f =>
    bAnd(Nat.blt f n, Nat.blt (pg w m p f) (pg w m q f)))

@[expose] noncomputable def sumL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.add x ih) l

@[expose] noncomputable def slpChk (T : Nat → Nat) (sh lm rb rm K a b c idn em eb iw im : Nat)
    (seeds : List Nat) (i : Nat) : Bool :=
  strictB (rgetL T sh lm rb rm i) (fun r =>
  strictB (Nat.land r em) (fun v =>
  strictB fld(r, eb, nat_lit 15) (fun op =>
  strictB fld(r, Nat.add eb (nat_lit 4), im) (fun x =>
  strictB fld(r, Nat.add eb (Nat.add (nat_lit 4) iw), nat_lit 18446744073709551615) (fun y =>
  strictB fld(r, Nat.add eb (Nat.add (nat_lit 68) iw), nat_lit 255) (fun nb =>
  bIf(Nat.beq op (nat_lit 0), bAnd(Nat.blt x (llen seeds), Nat.beq v (lnth seeds x)),
  bAnd(Nat.blt x i,
  bIf(Nat.beq op (nat_lit 1), bAnd(Nat.blt y i,
      Nat.beq v (mulK K a b c (elt T sh lm rb rm em x) (elt T sh lm rb rm em y))),
  bIf(Nat.beq op (nat_lit 2), Nat.beq (mulK K a b c v (elt T sh lm rb rm em x)) idn,
  bIf(Nat.beq op (nat_lit 3), Nat.beq v (powK K a b c idn (elt T sh lm rb rm em x) y nb),
    false)))))))))))

@[expose] noncomputable def slpRange (T : Nat → Nat) (sh lm rb rm K a b c idn em eb iw im : Nat)
    (seeds : List Nat) (lo cnt : Nat) : Bool :=
  allL cnt (fun j => slpChk T sh lm rb rm K a b c idn em eb iw im seeds (Nat.add lo j))

@[expose] noncomputable def actOK (T : Nat → Nat) (sh lm rb rm em K a b c x P aw am n : Nat) : Bool :=
  bAnd(Nat.blt P (Nat.shiftLeft (nat_lit 1) (Nat.mul aw n)),
    allL n (fun i => strictB fld(P, Nat.mul aw i, am) (fun p =>
      bAnd(Nat.blt p n, Nat.beq (mulK K a b c (elt T sh lm rb rm em p) x)
        (mulK K a b c x (elt T sh lm rb rm em i))))))

@[expose] noncomputable def fixCnt (n w m p : Nat) : Nat :=
  foldL n (fun i s => nIf(Nat.beq (pg w m p i) i, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def isId (n w m p : Nat) : Bool := Nat.beq (fixCnt n w m p) n

@[expose] noncomputable def restrOK (w m p PT pw pm k ρ rw rm : Nat) : Bool :=
  bAnd(Nat.blt ρ (Nat.shiftLeft (nat_lit 1) (Nat.mul rw k)),
    allL k (fun j => strictB (pg rw rm ρ j) (fun t =>
      bAnd(Nat.blt t k, Nat.beq (pg pw pm PT t) (pg w m p (pg pw pm PT j))))))

@[expose] noncomputable def ptsOK (n PT pw pm k : Nat) : Bool :=
  bAnd(Nat.blt (pg pw pm PT (Nat.sub k (nat_lit 1))) n,
    allL (Nat.sub k (nat_lit 1)) (fun j => Nat.blt (pg pw pm PT j) (pg pw pm PT (Nat.succ j))))

@[expose] noncomputable def isPerm (n b c p : Nat) : Bool :=
  bAnd(Nat.blt p (Nat.shiftLeft (nat_lit 1) (Nat.mul b n)),
    Nat.beq (foldL n (fun i s => strictN (pg b c p i) (fun v =>
      nIf(Nat.blt v n, Nat.lor s (Nat.shiftLeft (nat_lit 1) v), nat_lit 0))) (nat_lit 0))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))

end CFSG.KC.Local

end
