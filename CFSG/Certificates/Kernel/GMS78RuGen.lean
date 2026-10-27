module

public import Certificates.Data.GMS78RuNModel
public import Certificates.Data.GMS78RuSModelData

public section

namespace CFSG.KC.GMS.Gen

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuS CFSG.GMS78RuN

@[expose] def mul8 (mt : Array (Fin 8)) (a b : Fin 8) : Fin 8 := mt.getD (8 * a.val + b.val) 0

@[expose] def sqN (mt : Array (Fin 8)) (c e : Fin 8) (x : V3) : Fin 8 :=
  let u2 := mul8 mt x.1 x.1
  let ur := mul8 mt x.1 x.2.1
  mul8 mt (mul8 mt u2 u2) x.1 ^^^ mul8 mt c (mul8 mt ur ur) ^^^ mul8 mt (e ^^^ x.2.2) x.2.1

@[expose] def commN (mt : Array (Fin 8)) (c : Fin 8) (x z : V3) : Fin 8 :=
  let x2 := mul8 mt x.1 x.1
  let z2 := mul8 mt z.1 z.1
  let a := mul8 mt x.1 z.2.1
  let b := mul8 mt z.1 x.2.1
  mul8 mt x.1 (mul8 mt z2 z2) ^^^ mul8 mt (mul8 mt x2 x2) z.1 ^^^ mul8 mt c (mul8 mt a a ^^^ mul8 mt b b) ^^^
    mul8 mt x.2.2 z.2.1 ^^^ mul8 mt z.2.2 x.2.1

@[expose] def spanAt (mt : Array (Fin 8)) (c e : Fin 8) (W : List V3) (x : V3) : Bool :=
  W.any fun z₁ => commN mt c x z₁ == 0 &&
    (let q₁ := sqN mt c e z₁
     q₁ != 0 && W.any fun z₂ => commN mt c x z₂ == 0 &&
       (let q₂ := sqN mt c e z₂
        q₂ != 0 && q₂ != q₁ && W.any fun z₃ => commN mt c x z₃ == 0 && indep3 q₁ q₂ (sqN mt c e z₃)))

@[expose] def c1Check (mt : Array (Fin 8)) : Bool :=
  all8.all fun c => c == 0 || all8.all fun e => all8.all fun p => all8.all fun q =>
    !canon p q || (let W := wList p q
      W.all fun x => x.1 == 0 || x.2.1 == 0 || sqN mt c e x != 0 || spanAt mt c e W x)

@[expose] def c2Check (mt : Array (Fin 8)) (sl : List (Fin 8 × Fin 8 × Fin 8 × Fin 8)) : Bool :=
  all8.all fun c => c == 0 || all8.all fun e => all8.all fun p => all8.all fun q =>
    !canon p q || sl.contains (c, e, p, q) ||
      (let zs := (wList p q).filter fun x => allNZ x && sqN mt c e x == 0
       let ls := lineList p q
       zs.all fun x => zs.all fun y => x == y || commN mt c x y != 0 || !allNZ (addV x y) ||
         !(ls.all fun z => (commN mt c x z == 0) == (commN mt c y z == 0)))

@[expose] def candTab (mt : Array (Fin 8)) (c e : Fin 8) (W : List V3) : List (List V3) :=
  all8.map fun t => W.filter fun w => sqN mt c e w == t

@[expose] def isoExt (mt : Array (Fin 8)) (tab : List (List V3)) (c e : Fin 8) :
    List V3 → List (V3 × V3) → Bool
  | [], done => done.all fun pr => pr.1 == pr.2
  | b :: bs, done =>
    let tgt := done.map fun pr => (pr.2, commN mt c pr.1 b)
    (tab.getD (sqN mt c e b).val []).all fun w =>
      !(tgt.all fun pr => commN mt c pr.1 w == pr.2) || isoExt mt tab c e bs ((b, w) :: done)

@[expose] def c3Check (mt : Array (Fin 8)) : Bool :=
  all8.all fun c => all8.all fun e => all8.all fun p => all8.all fun q =>
    !canon p q || isoExt mt (candTab mt c e (wList p q)) c e (basisList p q) []

@[expose] def qC (qt : List (Fin 8)) (m : Nat) : Fin 8 := qt.getD m 0

@[expose] def bC (qt : List (Fin 8)) (m n : Nat) : Fin 8 := qC qt (m ^^^ n) ^^^ qC qt m ^^^ qC qt n

@[expose] def q0Check (mt : Array (Fin 8)) (qt : List (Fin 8))
    (sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3)) : Bool :=
  sd.all fun d => (List.range 256).all fun m => sqN mt d.1.1 d.1.2.1 (xiApply d.2.2 m) == qC qt m

@[expose] def s0Check (sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3))
    (sl : List (Fin 8 × Fin 8 × Fin 8 × Fin 8)) : Bool :=
  sd.map Prod.fst == sl &&
  (glList.all fun r => linComp r (linInv r) == linId && linComp (linInv r) r == linId &&
    m3Eq (bmul (rhoMat r) (rhoMat (linInv r))) m3One &&
    m3Eq (bmul (rhoMat (linInv r)) (rhoMat r)) m3One) &&
  (all256.all fun m => matToSl (slToMat m) == m) &&
  (glList.all fun r => let A := adMat r
    all256.all fun m => m3Eq (slToMat (maskApply A m))
      (bmul (bmul (rhoMat r) (slToMat m)) (rhoMat (linInv r)))) &&
  sd.all fun d =>
    ((wList d.1.2.2.1 d.1.2.2.2).all fun w =>
      xiApply d.2.2 (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w) == w) &&
    all256.all fun m => xApply d.2.1 d.1.2.2.1 d.1.2.2.2 (xiApply d.2.2 m) == m &&
      (lamList d.1.2.2.1 d.1.2.2.2).contains (xiApply d.2.2 m).2.2

@[expose] def s1Check (mt : Array (Fin 8))
    (sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3)) : Bool :=
  sd.all fun d =>
    glList.all fun r =>
      let A := adMat r
      (wList d.1.2.2.1 d.1.2.2.2).all fun w =>
        sqN mt d.1.1 d.1.2.1 (xiApply d.2.2 (maskApply A (xApply d.2.1 d.1.2.2.1 d.1.2.2.2 w))) ==
          linApply r (sqN mt d.1.1 d.1.2.1 w)

@[expose] def linIdx (r : Lin8) : Nat := r.1.val * 64 + r.2.1.val * 8 + r.2.2.val

@[expose] def incIdx : List Lin8 → Bool
  | a :: b :: l => decide (linIdx a < linIdx b) && incIdx (b :: l)
  | _ => true

@[expose] def glOK (gl : List Lin8) : Bool :=
  gl.length == 168 && incIdx gl && gl.all fun r => indep3 r.1 r.2.1 r.2.2

@[expose] def invListOK (il : List Lin8) : Bool :=
  il.length == 21 && incIdx il &&
    il.all fun r => indep3 r.1 r.2.1 r.2.2 && r != linId && linComp r r == linId

@[expose] def s2aCheckG (il : List Lin8) : Bool :=
  il.all fun r₁ => il.all fun r₂ =>
    r₁ == r₂ || linComp r₁ r₂ != linComp r₂ r₁ ||
      (let A₁ := adMat r₁
       let A₂ := adMat r₂
       decide ((all256.filter fun m => maskApply A₁ m == m && maskApply A₂ m == m).length ≤ 4))

@[expose] def s2bCheckG (il gl : List Lin8) : Bool :=
  il.all fun r₁ => il.all fun r₂ =>
    r₁ == r₂ || linComp r₁ r₂ != linComp r₂ r₁ ||
      gl.all fun r => linComp r r₁ != linComp r₁ r || linComp r r₂ != linComp r₂ r ||
        [linId, r₁, r₂, linComp r₁ r₂].contains r

@[expose] def sMaskN (sb : List Nat) (c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sMaskN sb c n ^^^ (if c.testBit n then sb.getD n 0 else 0)

@[expose] def sMask (sb : List Nat) (c : Nat) : Nat := sMaskN sb c 8

@[expose] def gamN (qt : List (Fin 8)) (sb : List Nat) (c c' : Nat) : Nat → Fin 8
  | 0 => 0
  | n + 1 =>
    gamN qt sb c c' n ^^^ (if c.testBit n then bC qt (sb.getD n 0) (sMaskN sb c' n) else 0)

@[expose] def gam (qt : List (Fin 8)) (sb : List Nat) (c c' : Nat) : Fin 8 := gamN qt sb c c' 8

@[expose] def dPartN (qt : List (Fin 8)) (sb : List Nat) (d : Fin 8) (c : Nat) : Nat → Nat × Fin 8
  | 0 => (0, 0)
  | n + 1 =>
    if c.testBit n then
      ((dPartN qt sb d c n).1 ^^^ 2 ^ (dMul d (fin8Of n)).val,
        (dPartN qt sb d c n).2 ^^^ gam qt sb (dPartN qt sb d c n).1 (2 ^ (dMul d (fin8Of n)).val))
    else dPartN qt sb d c n

@[expose] def dPart (qt : List (Fin 8)) (sb : List Nat) (d : Fin 8) (c : Nat) : Nat × Fin 8 :=
  dPartN qt sb d c 8

@[expose] def dCode (dct : List Lin8) (d : Fin 8) : Lin8 := dct.getD d.val linId

@[expose] def nB (nb : List Nat) (j : Nat) : Nat := nb.getD j 0

@[expose] def nCo (nc : List Nat) (m : Nat) : Nat := maskApply nc m

@[expose] def nBT (nbt : List (List (Fin 8))) (j i : Nat) : Fin 8 := (nbt.getD j []).getD i 0

@[expose] def nBeta (nbt : List (List (Fin 8))) (nc : List Nat) (m n : Nat) : Fin 8 :=
  xs8 (nCo nc m) fun j => xs8 (nCo nc n) (nBT nbt j)

@[expose] def nGam (nbt : List (List (Fin 8))) (nc : List Nat) (r : Lin8) (m n : Nat) : Fin 8 :=
  nBeta nbt nc (nAd r m) (nAd r n) ^^^ linApply r (nBeta nbt nc m n)

@[expose] def nQuad (nbt : List (List (Fin 8))) (nc nb : List Nat) (r : Lin8) (m : Nat) : Fin 8 :=
  xs8 (nCo nc m) fun j => xs8 (nCo nc m) fun i => if i < j then nGam nbt nc r (nB nb i) (nB nb j) else 0

@[expose] def nTw (ntw : List (List (Fin 8))) (r : Lin8) (j : Nat) : Fin 8 :=
  (ntw.getD (glList.idxOf r) []).getD j 0

@[expose] def nTau (nbt ntw : List (List (Fin 8))) (nc nb : List Nat) (r : Lin8) (m : Nat) : Fin 8 :=
  xs8 (nCo nc m) (nTw ntw r) ^^^ nQuad nbt nc nb r m

@[expose] def gamColCheck (qt : List (Fin 8)) (nbt : List (List (Fin 8))) (sb : List Nat) : Bool :=
  (List.range 8).all fun j => (List.range 256).all fun c =>
    xs8 c (nBT nbt j) == bC qt (sb.getD j 0) (sMaskN sb c j)

@[expose] def dPartCheck (qt : List (Fin 8)) (nbt ntw : List (List (Fin 8))) (sb nc nb : List Nat)
    (dct : List Lin8) : Bool :=
  (List.finRange 8).all fun d => (List.range 256).all fun c =>
    sMask sb (dPart qt sb d c).1 == nAd (dCode dct d) (sMask sb c) &&
      (dPart qt sb d c).2 == nTau nbt ntw nc nb (dCode dct d) (sMask sb c)

end CFSG.KC.GMS.Gen

end
