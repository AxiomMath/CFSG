module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Tree
public import Batteries.Data.ByteArray

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

@[inline, expose] def hexVal (d : UInt8) : ℕ := if d.toNat < 58 then d.toNat - 48 else d.toNat - 55

@[expose] def hexAtN (b : ByteArray) (o : ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => hexAtN b o w * 16 + hexVal (b.get! (o + w))

structure OmData where
  zc : Array ℕ
  gw : List (List ℕ)
  seedW : List (List ℕ)
  hex : String
  N : ℕ
  cIdx : ℕ
  schW : List (List ℕ)
  hN : ℕ
  hpar : List ℕ
  hsym : List ℕ

@[expose] def treeSize (pts : Array (Array ℕ × ℕ)) (k : ℕ) : ℕ :=
  ((List.range pts.size).filter fun n => (pts[n]!).2 == k).length

@[expose] def treeSizes (pts : Array (Array ℕ × ℕ)) : List ℕ := (List.range 5).map (treeSize pts)

@[expose] def subsetOK (N : ℕ) (sz : ℕ → ℕ) : Bool :=
  [false, true].all fun a => [false, true].all fun b => [false, true].all fun c =>
    [false, true].all fun d =>
      N % (1 + (if a then sz 1 else 0) + (if b then sz 2 else 0) + (if c then sz 3 else 0) +
        (if d then sz 4 else 0)) != 0 || (!a && !b && !c && !d) || (a && b && c && d)

@[expose] def quadOK (zc : Array ℕ) : Bool :=
  (List.range 36).all fun t => (mulCode zc zc)[t]! ^^^ zc[t]! ^^^ idCode[t]! == 0

@[expose] def epsOK (zc : Array ℕ) (gw : List (List ℕ)) : Bool :=
  (List.range 4).all fun j =>
    mulCode (mulCode (wordCode gw[j]!) zc) (wordCode (gw[j]!).reverse) ==
      (if j % 2 = 1 then mulCode zc zc else zc)

@[expose] def revInvOK (w : List ℕ) : Bool :=
  mulCode (wordCode w) (wordCode w.reverse) == idCode &&
    mulCode (wordCode w.reverse) (wordCode w) == idCode

namespace OmData

variable (D : OmData)

@[expose] def sc : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun s =>
    if s.val < 4 then wordCode D.gw[s.val]! else wordCode (D.gw[s.val - 4]!).reverse

@[expose] def sic : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun s =>
    if s.val < 4 then wordCode (D.gw[s.val]!).reverse else wordCode D.gw[s.val - 4]!

end OmData

@[expose] def schCode (scA : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldl (fun A s => mulCode A scA[s]!) idCode

@[expose] def schInv (sicA : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.reverse.foldl (fun A s => mulCode A sicA[s]!) idCode

namespace OmData

variable (D : OmData)

@[expose] def seedCode (w : List ℕ) : Array ℕ :=
  canonCode (conjCode (wordCode w) (wordCode w.reverse) D.zc)

@[expose] def roots : Array (Array ℕ) :=
  Array.ofFn (n := 5) fun k =>
    if k.val = 0 then canonCode D.zc else D.seedCode D.seedW[k.val - 1]!

@[expose] def forest : TreeData :=
  let b := D.hex.toUTF8
  { R := 5
    N := D.N
    roots := D.roots
    gens := Array.ofFn (n := 4) fun s => wordCode D.gw[s.val]!
    ginvs := Array.ofFn (n := 4) fun s => wordCode (D.gw[s.val]!).reverse
    par := fun n => hexAtN b (6 * n) 5
    sym := fun n => hexAtN b (6 * n + 5) 1 }

@[expose] def hTree (scA sicA : Array (Array ℕ)) (pts : Array (Array ℕ × ℕ)) : TreeData :=
  let hp := D.hpar.toArray
  let hs := D.hsym.toArray
  { R := 1
    N := D.hN
    roots := #[(pts[D.cIdx]!).1]
    gens := Array.ofFn (n := 8) fun t => schCode scA D.schW[t.val]!
    ginvs := Array.ofFn (n := 8) fun t => schInv sicA D.schW[t.val]!
    par := fun n => hp[n]!
    sym := fun n => hs[n]! }

@[expose] def check : Bool :=
  let scA := D.sc
  let sicA := D.sic
  let pts := D.forest.build
  let ht := D.hTree scA sicA pts
  let hpts := ht.build
  let sizes := treeSizes pts
  D.forest.ok && ht.ok && pts.size == D.N && D.N == 130816 && D.hN == 1024 &&
    D.gw.length == 4 && D.seedW.length == 4 && D.schW.length == 8 && D.cIdx < D.N &&
    D.gw.all revInvOK && D.seedW.all revInvOK && quadOK D.zc && epsOK D.zc D.gw &&
    D.schW.all (fun w => w.all (· < 8)) &&
    distinctOK (pts.toList.map (·.1)) && distinctOK (hpts.toList.map (·.1)) &&
    subsetOK D.N (fun k => sizes[k]!) && sizes[0]! == 1 && 32319 ≤ sizes[1]! &&
    D.schW.all fun w =>
      canonCode (conjCode (schCode scA w) (schInv sicA w) (pts[1]!).1) == (pts[1]!).1

end OmData

end CFSG.AGLEmbedding.KFactProofs.G28
