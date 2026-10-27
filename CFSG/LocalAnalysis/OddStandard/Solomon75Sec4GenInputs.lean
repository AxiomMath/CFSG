module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataInputs

public section

namespace CFSG.OddStandard.Solomon75.AhatData

@[expose] def genGSw (n : Nat) : List (List (Nat × Nat)) :=
  if n = 8 then
    [[(5, 6), (4, 7), (3, 7), (2, 6), (1, 2), (0, 3)], [(5, 7), (4, 6), (3, 7), (2, 5), (1, 5),
      (0, 3)], [(6, 7), (5, 6), (4, 5), (2, 3), (1, 3), (0, 1)]]
  else
    [[(9, 10), (8, 9), (5, 7), (4, 6), (3, 7), (2, 5), (1, 5), (0, 3)],
      [(8, 9), (6, 7), (5, 7), (4, 6), (3, 5), (2, 6), (1, 6), (0, 4)],
      [(7, 8), (6, 9), (5, 10), (4, 5), (3, 7), (2, 8), (1, 6), (0, 9)]]

@[expose] def genWord (n : Nat) : List Nat :=
  if n = 8 then [0, 0, 2, 2, 2, 1, 2, 1] else [2, 2, 2, 2]

@[expose] def swOK (n : Nat) (sw : List (Nat × Nat)) (even : Bool) : Bool :=
  sw.all (fun p => decide (p.1 < n) && decide (p.2 < n) && decide (p.1 ≠ p.2)) &&
    (!even || decide (sw.length % 2 = 0))

end CFSG.OddStandard.Solomon75.AhatData
