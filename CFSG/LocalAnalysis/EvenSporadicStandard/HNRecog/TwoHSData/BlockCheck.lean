module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

structure BlkData where
  k : ℕ
  blk : Array ℕ
  gens : List (List ℕ)
  labs : List Table

@[expose] def specWord (gs : List (List ℕ)) (spec : List (ℕ × ℕ)) : List ℕ :=
  spec.flatMap fun p => (List.replicate p.2 (gs.getD (p.1 - 1) [])).flatten

@[expose] def blkOfString (s : String) : Array ℕ := (s.toList.map fun c => c.toNat - 48).toArray

@[expose] def blkMapOK (k : ℕ) (b : Array ℕ) (T L : Table) : Bool :=
  allIn 0 1408 fun p => if b[p]! < k then b[ap T p]! == ap L b[p]! else decide (k ≤ b[ap T p]!)

@[expose] def blkTrivOK (b : Array ℕ) (T : Table) : Bool := allIn 0 1408 fun p => b[ap T p]! == b[p]!

@[expose] def blkSurjOK (k : ℕ) (b : Array ℕ) : Bool := (List.range k).all fun j => b.any (· == j)

@[expose] def blkDataOK (d : BlkData) : Bool :=
  gensOK && d.blk.size == 1408 && d.blk.all (· ≤ d.k) && blkSurjOK d.k d.blk &&
    d.gens.length == d.labs.length && d.gens.all wordOK && d.labs.all (permOK d.k) &&
    (d.gens.zip d.labs).all fun q => blkMapOK d.k d.blk (tabW q.1) q.2

@[expose] def pair4 (t0 ta tb tab : Table) : Array Table := #[t0, ta, tb, tab]

@[expose, noinline] def sqInOK (L V : Array Table) : Bool :=
  L.all fun s => memT 1408 V (compT 1408 s s)

@[expose, noinline] def trivInjOK (b : Array ℕ) (idt : Table) (L : Array Table) : Bool :=
  L.all fun s => !blkTrivOK b s || tblEq 1408 s idt

@[expose, noinline] def sqOneOK (idt : Table) (L : Array Table) : Bool :=
  L.all fun s => tblEq 1408 (compT 1408 s s) idt

@[expose] def blkImageOK (d : BlkData) (m : ℕ) : Bool := enumOK d.k 100000 m d.labs

end CFSG.EvenSporadicStandard.HNRecog
