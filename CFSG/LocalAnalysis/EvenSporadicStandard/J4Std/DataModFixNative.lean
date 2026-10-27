module

public import CFSG.Sporadic.J4.QTMask

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open CFSG.Sporadic.J4.QT

@[expose] def fixWords : Nat → List (List Int)
  | 1 => [[-3, -1, -1, -1], [2, 1, 3, 2]]
  | 3 => [[3, 2, 2], [-3, -3, -1, -3, -3], [-3, -1, -3, -3, 2, 1]]
  | _ => []

@[expose] def chkFixRoot (r : Nat) : Bool :=
  (fixWords r).all (fun s => s.all (fun ℓ => letters.contains ℓ) && s.foldr act r == r) &&
    (List.range 2048).all fun d =>
      (fixWords r).all (fun s => decide (s.foldr act d < 2048)) &&
        (!(fixWords r).all (fun s => s.foldr act d == d) || d == 0 || d == r)

@[expose] def chkFix : Bool := chkFixRoot 1 && chkFixRoot 3

end CFSG.EvenSporadicStandard.J4Std.DataMod
