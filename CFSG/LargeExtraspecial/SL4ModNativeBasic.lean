module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def mul4 (X Y : Array Nat) : Array Nat := mulRows 4 X Y

@[expose] def id4 : Array Nat := idRows 4

@[expose] def genCode : Nat → Array Nat
  | 0 => #[3, 2, 4, 8]
  | 1 => #[1, 6, 4, 8]
  | 2 => #[1, 2, 12, 8]
  | 3 => #[2, 1, 4, 8]
  | 4 => #[1, 4, 2, 8]
  | 5 => #[1, 2, 8, 4]
  | _ + 6 => #[1, 2, 4, 8]

@[expose] def uIdx (r c : Nat) : Nat := if r = 0 then c - 1 else if r = 1 then c + 1 else 5

@[expose] def uRow (e r : Nat) : Nat :=
  ofBits 4 fun c => c == r || (decide (r < c) && e.testBit (uIdx r c))

@[expose] def uCode (e : Nat) : Array Nat := Array.ofFn (n := 4) fun r => uRow e r.val

@[expose] def isUCode (R : Array Nat) : Bool :=
  (List.range 4).all fun r => (List.range 4).all fun c =>
    if c < r then !((R[r]?.getD 0).testBit c)
    else if c = r then (R[r]?.getD 0).testBit c else true

@[expose] def bitAt (R : Array Nat) (r c : Nat) : Nat := if (R[r]?.getD 0).testBit c then 1 else 0

@[expose] def uDecC (R : Array Nat) : Nat :=
  bitAt R 0 1 + 2 * bitAt R 0 2 + 4 * bitAt R 0 3 + 8 * bitAt R 1 2 + 16 * bitAt R 1 3 +
    32 * bitAt R 2 3

@[expose] def wordCode (w : List Nat) : Array Nat :=
  w.foldr (fun s acc => mul4 (genCode s) acc) id4

@[expose] def gCodeList : List Nat → List (Array Nat)
  | [] => [id4]
  | i :: ws =>
    (gCodeList ws).map (fun g => mul4 (genCode (i + 3)) g) ++
      (gCodeList ws).map (fun g => mul4 (mul4 (genCode i) (genCode (i + 3))) g)

end CFSG.LargeExtraspecial.SL4Mod.Native
