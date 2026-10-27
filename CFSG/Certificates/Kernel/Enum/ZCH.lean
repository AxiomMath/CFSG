module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def vChk (T : Nat → Nat) (sh lm rb rm n w m pm : Nat) (Z Zi : Nat → Nat)
    (VP VC : Nat → Nat) (h hi p o i : Nat) : Bool :=
  strictB (rperm T sh lm rb rm pm i) (fun u =>
    allN p (fun e => bAnd(eq3 n w m (VP (Nat.add o e)) (Z e) u (Zi e),
      strictB (VC (Nat.add o e)) (fun f =>
        bAnd(Nat.blt f p, eq3 n w m (VP (Nat.add o f)) h (VP (Nat.add o e)) hi)))))

@[expose] noncomputable def vRange (T : Nat → Nat) (sh lm rb rm n w m pm : Nat) (Z Zi : Nat → Nat)
    (VP VC : Nat → Nat) (h hi p lo cnt : Nat) : Bool :=
  allN cnt (fun t => vChk T sh lm rb rm n w m pm Z Zi VP VC h hi p (Nat.mul p t) (Nat.add lo t))

@[expose] noncomputable def hCi (T : Nat → Nat) (sh lm rb rm nw k : Nat) : Nat :=
  fld(rget T sh lm rb rm k, Nat.add nw (nat_lit 36), nat_lit 15)

@[expose] noncomputable def hChk (T : Nat → Nat) (sh lm rb rm n w m nw pm nH idn h1 h2 nR : Nat)
    (REP : Nat → Nat) (k : Nat) : Bool :=
  strictB (rget T sh lm rb rm k) (fun r =>
  strictB (Nat.land r pm) (fun e =>
  strictB fld(r, nw, nat_lit 255) (fun par =>
  strictB fld(r, Nat.add nw (nat_lit 8), nat_lit 15) (fun g =>
  strictB fld(r, Nat.add nw (nat_lit 12), nat_lit 255) (fun s1 =>
  strictB fld(r, Nat.add nw (nat_lit 20), nat_lit 255) (fun s2 =>
  strictB fld(r, Nat.add nw (nat_lit 28), nat_lit 255) (fun cu =>
  strictB fld(r, Nat.add nw (nat_lit 36), nat_lit 15) (fun ci =>
  bAnd(bIf(Nat.beq k (nat_lit 0), Nat.beq e idn,
      bAnd(Nat.blt par k, eq2 n w m e (rperm T sh lm rb rm pm par) (nIf(Nat.beq g (nat_lit 0), h1, h2)))),
  bAnd(Nat.blt s1 nH, bAnd(Nat.blt s2 nH,
  bAnd(eq2 n w m (rperm T sh lm rb rm pm s1) e h1, bAnd(eq2 n w m (rperm T sh lm rb rm pm s2) e h2,
  bIf(Nat.beq ci (nat_lit 15), Nat.beq e idn,
    bAnd(Nat.blt cu nH, bAnd(Nat.blt ci nR,
      strictB (rperm T sh lm rb rm pm cu) (fun su =>
        eq22 n w m e su su (rperm T sh lm rb rm pm (REP ci)))))))))))))))))))

@[expose] noncomputable def hRange (T : Nat → Nat) (sh lm rb rm n w m nw pm nH idn h1 h2 nR : Nat)
    (REP : Nat → Nat) (cnt : Nat) : Bool :=
  allN cnt (fun k => hChk T sh lm rb rm n w m nw pm nH idn h1 h2 nR REP k)

@[expose] noncomputable def lpt (T : Nat → Nat) (sh lm rb rm w m pm : Nat) (L : List Nat) (q : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun l _ ih q => strictN (ih q) (fun v => pg w m (rperm T sh lm rb rm pm l) v)) L q

@[expose] noncomputable def ncOK (T : Nat → Nat) (sh lm rb rm n w m nw pm nH : Nat) (h i : Nat)
    (L : List Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true
      (fun l _ ih => bAnd(Nat.blt l nH, bAnd(Nat.beq (hCi T sh lm rb rm nw l) i, ih))) L,
    allN n (fun q => Nat.beq (pg w m h q) (lpt T sh lm rb rm w m pm L q)))

end CFSG.KC.Enum

end
