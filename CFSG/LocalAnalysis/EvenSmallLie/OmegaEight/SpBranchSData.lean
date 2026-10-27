module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSTabData
public import Aesop.BuiltinRules
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def appK (k : ℕ) (g : List ℕ) (x : ℕ) : ℕ :=
  (List.range k).foldl (fun r j => if x.testBit j then r ^^^ g.getD j 0 else r) 0

@[expose] def app6 (g : List ℕ) (x : ℕ) : ℕ := appK 6 g x

@[expose] def mul6 (g h : List ℕ) : List ℕ := h.map (app6 g)

@[expose] def key6 (g : List ℕ) : ℕ := g.foldl (fun acc c => acc * 64 + c) 0

@[expose] def id6 : List ℕ := [1, 2, 4, 8, 16, 32]

@[expose] def p9Gens : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 36], [1, 2, 4, 8, 20, 34], [1, 2, 4, 9, 18, 32], [1, 2, 4, 10, 17, 32],
    [1, 2, 4, 12, 16, 33], [1, 2, 7, 40, 48, 32], [2, 1, 4, 16, 8, 32], [5, 6, 4, 8, 16, 56],
    [24, 27, 4, 9, 11, 32]]

@[expose] def closeRound (gens : List (List ℕ))
    (st : Std.HashSet ℕ × Array (List ℕ) × List (List ℕ)) :
    Std.HashSet ℕ × Array (List ℕ) × List (List ℕ) :=
  st.2.2.foldl (fun (acc : Std.HashSet ℕ × Array (List ℕ) × List (List ℕ)) x =>
    gens.foldl (fun (acc : Std.HashSet ℕ × Array (List ℕ) × List (List ℕ)) g =>
      let y := mul6 x g
      if acc.1.contains (key6 y) then acc else (acc.1.insert (key6 y), acc.2.1.push y, y :: acc.2.2))
      acc) (st.1, st.2.1, [])

@[expose] def closure6 (gens : List (List ℕ)) (fuel : ℕ) : Array (List ℕ) :=
  ((List.range fuel).foldl (fun st _ => closeRound gens st)
    ((∅ : Std.HashSet ℕ).insert (key6 id6), #[id6], [id6])).2.1

@[expose] def p9List : Array (List ℕ) :=
  ((closure6 p9Gens 40).toList.mergeSort fun a b => decide (key6 a ≤ key6 b)).toArray

@[expose] def p9Index : Std.HashMap ℕ ℕ :=
  (List.range p9List.size).foldl (fun m i => m.insert (key6 (p9List[i]!)) i) ∅

@[expose] def sAct : Array ℕ :=
  Array.ofFn (n := 65536) fun k => sActRow (k.val / 128) / 2 ^ (7 * (k.val % 128)) % 2 ^ 7

@[expose] def sMt : Array ℕ :=
  Array.ofFn (n := 262144) fun k => sMtRow (k.val / 512) / 2 ^ (9 * (k.val % 512)) % 2 ^ 9

@[expose] def sGinv : Array ℕ :=
  Array.ofFn (n := 512) fun k => sGinvLit / 2 ^ (9 * k.val) % 2 ^ 9

@[expose] def sMul (c d : ℕ) : ℕ :=
  ((c % 128) ^^^ sAct[(c / 128 % 512) * 128 + d % 128]!) + 128 * sMt[(c / 128 % 512) * 512 + d / 128 % 512]!

@[expose] def sInv (c : ℕ) : ℕ :=
  let gi := sGinv[c / 128 % 512]!
  sAct[gi * 128 + c % 128]! + 128 * gi

@[expose] def sA (g e : ℕ) : ℕ := sAct[g * 128 + e]!

@[expose] def sM (g h : ℕ) : ℕ := sMt[g * 512 + h]!

@[expose] def sRangeCheck : Bool :=
  sAct.size == 65536 && sMt.size == 262144 && sAct.all (· < 128) && sMt.all (· < 512) &&
    (List.range 512).all fun i => decide (sGinv[i]! < 512)

@[expose] def sAssocCheck : Bool :=
  (List.range 512).all fun i => (List.range 512).all fun j => (List.range 512).all fun k =>
    sM (sM i j) k == sM i (sM j k)

@[expose] def sUnitCheck : Bool :=
  (List.range 512).all fun j => sM 0 j == j && sM j 0 == j && sM (sGinv[j]!) j == 0

@[expose] def sActCheck : Bool :=
  ((List.range 512).all fun g => (List.range 128).all fun e => (List.range 128).all fun e' =>
    sA g (e ^^^ e') == (sA g e ^^^ sA g e')) &&
  ((List.range 512).all fun g => (List.range 512).all fun h => (List.range 128).all fun e =>
    sA (sM g h) e == sA g (sA h e)) &&
  (List.range 128).all fun e => sA 0 e == e

end CFSG.EvenSmallLie.OmegaEight.SpBranch
