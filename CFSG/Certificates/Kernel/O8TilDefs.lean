module

public import Certificates.Data.Kernel.O8.Til
public import CFSG.Certificates.Kernel.O8Z4Proved
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitZData

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

@[expose] def tilGetG (T : Array (Array ℕ)) (i : ℕ) : Array (Array ℕ) := dec4 (T.getD i #[])

@[expose] def tilIdxG (T : Array (Array ℕ)) (M : Array (Array ℕ)) : ℕ :=
  ((List.range 128).find? fun i => tilGetG T i == M).getD 128

@[expose] def centcG (T : Array (Array ℕ)) (M : Array (Array ℕ)) : ℕ :=
  ((List.range 128).filter fun j => mul4 M (tilGetG T j) == mul4 (tilGetG T j) M).length

@[expose] def xCheckG (q : ℕ → Bool) (n0 : ℕ) (G C : ℕ → Array ℕ) (X : Array ℕ)
    (RW : List (List ℕ)) : Bool :=
  let Xm := dec4 X
  let r := reflRowsG q n0
  mul4 Xm Xm == one4 && red2 Xm == r &&
    (List.range 6).all fun s => mul4 (mul4 Xm (ptil4G G C s)) Xm == prod4G G C (RW.getD s []) &&
      wordRowsG G (RW.getD s []) == bmul 6 6 r (bmul 6 6 (G s) r)

@[expose] def tabCheckG (G C U : ℕ → Array ℕ) (X : Array ℕ) (UW : List (List ℕ))
    (T : Array (Array ℕ)) : Bool :=
  tilGetG T 0 == one4 && tilIdxG T (dec4 X) < 128 &&
    ((List.range 6).all fun k => wordRowsG G (UW.getD k []) == U k &&
      tilIdxG T (prod4G G C (UW.getD k [])) < 128) &&
    ((List.range 128).all fun i => (List.range 128).all fun j =>
      tilIdxG T (mul4 (tilGetG T i) (tilGetG T j)) < 128) &&
    (List.range 128).all fun i => (List.range 128).all fun j =>
      i == j || !(red2 (tilGetG T i) == red2 (tilGetG T j))

@[expose] def invCheckSG (T : Array (Array ℕ)) (z : ℕ) : Bool :=
  (List.range 128).all fun i =>
    let M := tilGetG T i
    !isInvol4 M || (decide (128 * fix2c (red2 M) < 64 * fix4c M) &&
      (i == z || decide (256 < 2 * fix4c M) || decide (2 * fix4c M * centcG T M < 16384)))

@[expose] def tilCheckG (q : ℕ → Bool) (n0 : ℕ) (G C U : ℕ → Array ℕ) (X : Array ℕ)
    (RW UW : List (List ℕ)) (T : Array (Array ℕ)) (z : ℕ) : Bool :=
  xCheckG q n0 G C X RW && tabCheckG G C U X UW T && invCheckSG T z

@[expose] def tilGenG (G C : ℕ → Array ℕ) (X : Array ℕ) (UW : List (List ℕ)) (g : ℕ) :
    Array (Array ℕ) :=
  if g < 6 then prod4G G C (UW.getD g []) else dec4 X

@[expose] def zCountG (T : Array (Array ℕ)) (ann : List (Array ℕ)) (n : ℕ) : ℕ :=
  ((List.range 128).filter fun j =>
      ann.all fun f => dot4 f (mv4 (sub4 one4 (tilGetG T j)) (dig4 n)) == 0).length +
    ((List.range 128).filter fun j =>
      ann.all fun f => dot4 f (mv4 (add4 one4 (tilGetG T j)) (dig4 n)) == 0).length

@[expose] def zCheckG (G C : ℕ → Array ℕ) (X : Array ℕ) (UW : List (List ℕ))
    (T : Array (Array ℕ)) (tr : Array (ℕ × ℕ)) (z r : ℕ) (ann : List (Array ℕ))
    (wit : List (ℕ × ℕ × Bool)) : Bool :=
  let Tz := tilGetG T z
  let Tr := tilGetG T r
  ((List.range 127).all fun i =>
    let e := tr.getD (i + 1) (0, 0)
    decide (e.1 < i + 1) && decide (e.2 < 7) &&
      tilGetG T (i + 1) == mul4 (tilGenG G C X UW e.2) (tilGetG T e.1)) &&
    ((List.range 128).all fun j => mul4 Tz (tilGetG T j) == mul4 (tilGetG T j) Tz) &&
    fix4c Tz == 64 && decide (z < 128) && decide (r < 128) && mul4 Tr Tr == Tz &&
    (ann.all fun f => (List.range 4096).all fun n => dot4 f (mv4 (sub4 one4 Tz) (dig4 n)) == 0) &&
    (wit.all fun w => mv4 (if w.2.2 then add4 one4 Tr else sub4 one4 Tr) (dig4 w.2.1) == dig4 w.1) &&
    (List.range 4096).all fun n => !(mv4 (add4 one4 Tz) (dig4 n) == dig4 0) ||
      wit.any (fun w => w.1 == n) || decide (zCountG T ann n ≤ 128)

@[expose] def TilBind (T : Array (Array ℕ)) (TL : Nat) : Prop :=
  T.size = 128 ∧ ∀ i < 128, tilGetG T i = dec4M (tilAt TL i)

end CFSG.KC.O8

end
