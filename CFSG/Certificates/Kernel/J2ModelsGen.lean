module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CFSG.KC.J2Models

open CFSG.ComponentClassification.J2Cover.Models CFSG.Monster.B.Co2.Native

@[expose] def bitR (rf : Nat → Nat) (x y : Nat) : Bool := (rf x).testBit y

@[expose] def decompColsG (yD : Nat → Nat → Nat × Nat) (mtA : Array (Array Nat))
    (gn pr : Nat → Nat) : Array (Array Nat) × Array (Array Nat) := Id.run do
  let Y := (Array.ofFn (n := 3) fun k => Array.ofFn (n := 4725) fun i => yD k.val i.val)
  let mut pc : Array (Array Nat) := #[Array.replicate 4725 0]
  let mut ic : Array (Array Nat) := #[Array.ofFn (n := 4725) fun i => i.val]
  for a in [1:128] do
    let g := gn a
    let q := pr a
    let pq := pc[q]!
    let iq := ic[q]!
    let Yg := Y[g]!
    let mut pa : Array Nat := Array.replicate 4725 0
    let mut ia : Array Nat := Array.replicate 4725 0
    for i in [0:4725] do
      let pr := Yg[i]!
      pa := pa.set! i mtA[pr.1]![pq[pr.2]!]!
      ia := ia.set! i iq[pr.2]!
    pc := pc.push pa
    ic := ic.push ia
  return (pc, ic)

@[expose] def normCocOKG (mt lm : Nat → Nat → Nat) (rf : Nat → Nat) : Bool :=
  allLt 128 (fun x => !(bitR rf 0 x) && !(bitR rf x 0)) &&
  allLt 3 (fun k => allLt 128 fun b => allLt 128 fun c =>
    !(bitR rf (k + 1) b ^^ bitR rf (lm k b) c ^^ bitR rf b c ^^ bitR rf (k + 1) (mt b c)))

@[expose] def treeNormOKG (rf : Nat → Nat) : Bool :=
  allLt 128 fun x => x == 0 || !(bitR rf (gen x + 1) (par x))

@[expose] def cocycleCheckG (mt lm : Nat → Nat → Nat) (fR : Nat → Nat) (hR : Nat → Nat → Nat) :
    Bool :=
  normCocOKG mt lm fR &&
  allLt 6 (fun j => normCocOKG mt lm (hR j) && treeNormOKG (hR j) &&
    allLt 6 fun l => decide (qPos l < 384) &&
      bitR (hR j) (qPos l / 128 + 1) (qPos l % 128) == (j == l)) &&
  allLt 3 (fun k => (allLt 3 fun m => maskBit (chiMask k) (m + 1) == (k == m)) &&
    allLt 128 fun a => allLt 128 fun d =>
      maskBit (chiMask k) (mt a d) == (maskBit (chiMask k) a ^^ maskBit (chiMask k) d))

@[expose] def cobBitG (mt : Nat → Nat → Nat) (m a d : Nat) : Bool :=
  maskBit m a ^^ maskBit m d ^^ maskBit m (mt a d)

@[expose] def trBitG (pT iT : Nat → Nat → Nat) (rf : Nat → Nat) (a d : Nat) : Bool :=
  xorFold 4725 fun i => bitR rf (pT i a) (pT (iT i a) d)

@[expose] def transferCheckG (mt pT iT : Nat → Nat → Nat) (fR : Nat → Nat) (hR : Nat → Nat → Nat) :
    Bool :=
  allLt 6 (fun j => !(maskBit (bMask j) 0)) && !(maskBit muMask 0) &&
  allLt 6 (fun j => allLt 3 fun k => allLt 128 fun d =>
    trBitG pT iT (hR j) (k + 1) d ==
      ((eBit j && bitR fR (k + 1) d) ^^ cobBitG mt (bMask j) (k + 1) d)) &&
  allLt 3 (fun k => allLt 128 fun d =>
    (trBitG pT iT fR (k + 1) d ^^ cobBitG mt muMask (k + 1) d) == bitR fR (k + 1) d)

@[expose] def cBitG (mt pT iT : Nat → Nat → Nat) (bt it aC : Nat → Nat) (fR : Nat → Nat)
    (i a : Nat) : Bool :=
  let s := aC i
  let si := it s
  let p := pT i a
  let bp := bt p
  bitR fR si s ^^ lamBit p ^^ bitR fR si bp ^^ bitR fR (mt si bp) (aC (iT i a))

@[expose] def lambdaCheckG (mt pT iT : Nat → Nat → Nat) (bt it aC : Nat → Nat) (fR : Nat → Nat) :
    Bool :=
  !(lamBit 0) &&
  allLt 128 (fun a => allLt 128 fun d =>
    (bitR fR a d ^^ bitR fR (bt a) (bt d)) == cobBitG mt lamMask a d) &&
  allLt 128 (fun a => !(lamBit a ^^ lamBit (bt a))) &&
  allLt 128 (fun a =>
    (xorFold 4725 (fun i => cBitG mt pT iT bt it aC fR i a) ^^ muBit a ^^ muBit (bt a)) == lamBit a)

@[expose] def mulRG (mt : Nat → Nat → Nat) (fR : Nat → Nat) (c c' : Nat) : Nat :=
  mt (c % 128) (c' % 128) +
    128 * ((c / 128 + c' / 128 + (if bitR fR (c % 128) (c' % 128) then 1 else 0)) % 2)

@[expose] def tauCG (bt : Nat → Nat) (c : Nat) : Nat :=
  bt (c % 128) + 128 * ((c / 128 + (if lamBit (c % 128) then 1 else 0)) % 2)

@[expose] def mulTG (mt : Nat → Nat → Nat) (bt : Nat → Nat) (fR : Nat → Nat) (eps c c' : Nat) :
    Nat :=
  let r := mulRG mt fR (c % 256) (if c / 256 = 1 then tauCG bt (c' % 256) else c' % 256)
  (if eps = 1 ∧ c / 256 = 1 ∧ c' / 256 = 1 then mulRG mt fR r 128 else r) +
    256 * ((c / 256 + c' / 256) % 2)

@[expose] def groupCheckG (mt : Nat → Nat → Nat) (bt : Nat → Nat) (fR : Nat → Nat) : Bool :=
  centerOK 256 (mulRG mt fR) && rootCounts 256 (mulRG mt fR) == [(0, 0), (48, 0), (40, 96)] &&
  centerOK 512 (mulTG mt bt fR 0) &&
    rootCounts 512 (mulTG mt bt fR 0) == [(0, 0), (48, 64), (56, 160)] &&
  centerOK 512 (mulTG mt bt fR 1) &&
    rootCounts 512 (mulTG mt bt fR 1) == [(16, 0), (96, 64), (40, 160)]

theorem decompCols_eq : decompCols = decompColsG yDecomp mulTab gen par := by
  unfold decompCols
  rfl

theorem cocycleCheck_eq : cocycleCheck = cocycleCheckG (fun a d => mulTab[a]![d]!)
    (fun k b => lmulTab[k]![b]!) (fun x => fRows[x]!) (fun j x => (hRowsT j)[x]!) := rfl

theorem transferCheck_eq : transferCheck =
    transferCheckG (fun a d => mulTab[a]![d]!) pTab iTab (fun x => fRows[x]!)
      (fun j x => (hRowsT j)[x]!) := rfl

theorem lambdaCheck_eq : lambdaCheck = lambdaCheckG (fun a d => mulTab[a]![d]!) pTab iTab
    (fun a => betaTab[a]!) (fun a => invTab[a]!) (fun i => aCoefT[i]!) (fun x => fRows[x]!) := rfl

theorem groupCheck_eq : groupCheck =
    groupCheckG (fun a d => mulTab[a]![d]!) (fun a => betaTab[a]!) (fun x => fRows[x]!) := rfl

end CFSG.KC.J2Models

end
