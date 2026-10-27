module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJInputs
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

@[expose] def genU : List ℕ :=
  [3169, 962, 1091, 3184, 2528, 1846, 752, 898, 526, 2555, 1665, 1967, 1448, 2576, 195, 1150,
    594, 1718, 3199, 2661, 190, 2631]

@[expose] def genUSorted : List ℕ :=
  [190, 195, 526, 594, 752, 898, 962, 1091, 1150, 1448, 1665, 1718, 1846, 1967, 2528, 2555,
    2576, 2631, 2661, 3169, 3184, 3199]

@[expose] def genChecksA (O : WOrbit) : Bool :=
  let e := starPts (dTable O)
  (List.range 22).all fun j =>
    e[starPhiPos[genU.getD j 0]!]! == FrameJ.fjPts.getD (j + 1) 0

@[expose] def genCertA : Bool := genChecksA (CFSG.Sporadic.Fi23.Native.orbitData ())

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen
