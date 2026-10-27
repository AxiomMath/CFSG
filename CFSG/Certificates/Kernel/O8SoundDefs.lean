module

public import Certificates.Data.Kernel.O8.Core
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Data

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

@[expose] noncomputable def decR (P : Nat) : Array Nat :=
  #[frow P 0, frow P 1, frow P 2, frow P 3, frow P 4, frow P 5]

@[expose] def QBind (q : ℕ → Bool) (Q : Nat) : Prop := ∀ x < 64, q x = Nat.testBit Q x

@[expose] def bfG (q : ℕ → Bool) (x y : ℕ) : Bool := q (x ^^^ y) ^^ q x ^^ q y

@[expose] def reflBG (q : ℕ → Bool) (v x : ℕ) : ℕ := x ^^^ (if bfG q x v then v else 0)

@[expose] def reflRowsG (q : ℕ → Bool) (v : ℕ) : Array ℕ :=
  Array.ofFn (n := 6) fun i => bitsOf 6 fun j => (reflBG q v (2 ^ j)).testBit i

@[expose] def wordRowsG (G : ℕ → Array ℕ) (w : List ℕ) : Array ℕ :=
  w.foldr (fun s acc => bmul 6 6 (G s) acc) id6

@[expose] def ptil4G (G C : ℕ → Array ℕ) (s : ℕ) : Array (Array ℕ) :=
  add4 (lift2 (G s)) (add4 (lift2 (C s)) (lift2 (C s)))

@[expose] def prod4G (G C : ℕ → Array ℕ) (w : List ℕ) : Array (Array ℕ) :=
  w.foldr (fun s acc => mul4 (ptil4G G C s) acc) one4

end CFSG.KC.O8

end
