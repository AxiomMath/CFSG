module

public import CFSG.Sporadic.J4.QTNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.EvenSporadicStandard.J4Std.Data11

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (duadMasks)

@[expose] def pWord : List Int := (List.replicate 12 [1, 2, 3]).flatten

@[expose] def qWord : List Int :=
  [2, 3, -1, -3, -1, 3, 1, 1, 3, 3, -1, -2, -2, 1, 1, 1, 3, -2, 3, 3, -1, -2, -3, -1, 3, -2, -1, 2,
    1, -3, 2, -1, 2, -1]

@[expose] def qMask : Nat := 667

@[expose] def u0Mask : Nat := 1843

@[expose] def chkPQ (loc inv : Array (Array V2)) : Bool :=
  let P := wordRows loc inv pWord
  let Q := mulRows (etaRows (uTab loc inv) 11 qMask) (wordRows loc inv qWord)
  eqRows (powRows P 11) idRows && eqRows (mulRows Q P) (mulRows (mulRows P P) Q)

@[expose] def pTab : List Nat := [1765, 1312, 411, 2001, 431, 1558, 580, 1506, 803, 29, 113]

@[expose] def pRow (j : Nat) : Nat := pTab.getD j 0

@[expose] def pMap (c : Nat) : Nat := rowsXor pRow 11 c

@[expose] def pPow : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => pMap (pPow k c)

@[expose] def evAt (y f : Nat) : Nat := rowsXor (fun i => pPow i y) 11 f

@[expose] def MaskFacts : Prop :=
  (∀ j < 11, pWord.foldr act (2 ^ j) = pRow j) ∧
  (∀ j < 11, pRow j < 2 ^ 11) ∧
  pMap 2 ≠ 2 ∧
  pMap u0Mask = u0Mask ∧
  (∀ c < 2 ^ 11, pMap c = c → c = 0 ∨ c = u0Mask) ∧
  ((List.range (2 ^ 11)).map (evAt 1)).Nodup ∧
  (∀ f < 2 ^ 11, ∀ k < 11, evAt (evAt 1 f) f = pPow k 1 → ∃ m < 11, evAt 1 f = pPow m 1) ∧
  (∀ f < 2 ^ 11, (∀ g < 2 ^ 11, evAt 1 g ∈ duadMasks → evAt (evAt 1 f) g ∈ duadMasks) →
    ∃ m < 11, evAt 1 f = pPow m 1)

set_option synthInstance.maxSize 1024 in
instance : Decidable MaskFacts := by unfold MaskFacts; infer_instance

@[expose] def chkMask : Bool := decide MaskFacts

end CFSG.EvenSporadicStandard.J4Std.Data11
