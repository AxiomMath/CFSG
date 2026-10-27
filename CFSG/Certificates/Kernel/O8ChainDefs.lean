module

public import CFSG.Certificates.Kernel.O8SoundDefs

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain CFSG.KLie.CT

@[expose] def s0GetG (S : Array (Array ℕ)) (i : ℕ) : Array ℕ := S.getD i id6

@[expose] def s0IdxG (S : Array (Array ℕ)) (M : Array ℕ) : ℕ := (S.findIdx? (· == M)).getD 64

@[expose] def mulTabG (S : Array (Array ℕ)) : Array (Array ℕ) :=
  Array.ofFn (n := 64) fun i => Array.ofFn (n := 64) fun j =>
    s0IdxG S (bmul 6 6 (s0GetG S i) (s0GetG S j))

@[expose] def fixMaskG (S : Array (Array ℕ)) (m : ℕ) : ℕ :=
  ((List.range 64).filter fun z => (List.range 64).all fun a =>
    !m.testBit a || bmulVec 6 6 (s0GetG S a) z == z).length

@[expose] def treeOkG (S : Array (Array ℕ)) (U : ℕ → Array ℕ) (tr : Array (ℕ × ℕ)) (i : ℕ) :
    Bool :=
  let e := tr.getD i (0, 0)
  e.2 < i && e.1 < 6 && bmul 6 6 (U e.1) (s0GetG S e.2) == s0GetG S i

@[expose] def s0CheckG (S : Array (Array ℕ)) (U : ℕ → Array ℕ) (tr : Array (ℕ × ℕ)) : Bool :=
  let T := mulTabG S
  S.size == 64 && s0GetG S 0 == id6 &&
    ((List.range 64).all fun i => (List.range 64).all fun j => i == j ||
      (List.range 64).any fun z => bmulVec 6 6 (s0GetG S i) z != bmulVec 6 6 (s0GetG S j) z) &&
    ((List.range 6).all fun k => s0IdxG S (U k) < 64 && s0GetG S (s0IdxG S (U k)) == U k) &&
    ((List.range 64).all fun i => (List.range 64).all fun j => tabGet T i j < 64 &&
      s0GetG S (tabGet T i j) == bmul 6 6 (s0GetG S i) (s0GetG S j)) &&
    ((List.range 64).all fun i => (List.range 64).any fun j => tabGet T i j == 0) &&
    ((List.range 64).all fun y => tabGet T 0 y == y) &&
    (List.range 63).all fun i => treeOkG S U tr (i + 1)

@[expose] def abelCheckG (S : Array (Array ℕ)) (L : List ℕ) : Bool :=
  let T := mulTabG S
  L.contains 1 && (L.all fun m => m < 2 ^ 64) &&
    (L.all fun m => (List.range 64).all fun y =>
      m.testBit y || !commAll T m y || L.contains (closeY T y 8 m)) &&
    L.all fun m => popcount64 m * fixMaskG S m ≤ 64

@[expose] def S0Bind (S : Array (Array ℕ)) (L : Nat) : Prop :=
  S.size = 64 ∧ ∀ i < 64, s0GetG S i = decR (mat L i)

end CFSG.KC.O8

end
