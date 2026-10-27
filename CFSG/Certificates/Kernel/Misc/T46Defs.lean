module

public import Certificates.Data.CFSGNative.F4.T46Simple
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.Misc.T46

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi22.Native

@[expose] def uPosG (U : Array Nat) : Array Nat :=
  Array.ofFn (n := 4096) fun c => U.toList.idxOf c.val

@[expose] def tvTableG (U : Array Nat) (v : Nat) : Table :=
  Array.ofFn (n := 693) fun k => UInt32.ofNat ((uPosG U)[normC (tvC v U[k.val]!)]!)

@[expose] def tvGensG (U : Array Nat) : Array Nat :=
  (U.filter fun c => weightC c == 2).push (1 + 4 + 16 + 64)

@[expose] def genG (U : Array Nat) (z : Int) : Table := tvTableG U (tvGensG U)[z.natAbs - 1]!

@[expose] def lettersG (U : Array Nat) (WS : List String) : Array Table :=
  buildLetters 693 (genG U) (WS.map wordOfInts).toArray

@[expose] def powG (U : Array Nat) (e : Nat) (w : List Int) : Table :=
  powT 693 e (wordT 693 (genG U) w)

@[expose] def xyGenG (U : Array Nat) (xw yw : List Int) (z : Int) : Table :=
  if z = 1 then powG U 3 xw else powG U 2 yw

@[expose] def subTreeG (U : Array Nat) (WS : List String) (B : Array Nat) (r : Nat) : Tree :=
  treeBFS 693 r (lettersG U WS) (levelLetters (lettersG U WS) B 1)

@[expose] def t46G (U : Array Nat) (WS : List String) (TW : Array (List Int)) (xw yw : List Int)
    (B : Array Nat) (r : Nat) : Bool :=
  let W := (WS.map wordOfInts).toArray
  let XT := powG U 3 xw
  let YT := powG U 2 yw
  W.size == 53 && allIn 0 46 (fun k => W[k]! == [(k : Int) + 1]) &&
    t46FixAll (tvTableG U 0) && t46FixAll (powT 693 2 XT) && !t46FixAll XT &&
    t46FixAll (powT 693 3 YT) && !t46FixAll YT &&
    t46FixAll (powT 693 11 (compT 693 XT YT)) && !t46FixAll (compT 693 XT YT) &&
    allIn 0 46 (fun k => t46TblEq (wordT 693 (xyGenG U xw yw) TW[k]!)
      (tvTableG U (tvGensG U)[k]!)) &&
    treeOK 693 r (subTreeG U WS B r) (lettersG U WS) (levelLetters (lettersG U WS) B 1) &&
    (subTreeG U WS B r).pts.size == 180 &&
    allIn 0 693 (fun p => p == 0 || t46InTree (chainTrees 693 (lettersG U WS) B)[1]! p ||
      t46InTree (subTreeG U WS B r) p)

@[expose] def wordStrings : List String :=
  ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16", "17", "18",
    "19", "20", "21", "22", "23", "24", "25", "26", "27", "28", "29", "30", "31", "32", "33", "34",
    "35", "36", "37", "38", "39", "40", "41", "42", "43", "44", "45", "46", "1", "12", "22", "35",
    "-19 -32 46 32 19", "-12 -19 -32 -46 32 19 -40 25 -19 -32 46 32 19 15",
    "-12 -15 -12 -19 -32 -46 32 19 -40 25 -19 -32 46 32 19 15 15 12"]

end CFSG.KC.Misc.T46

end
