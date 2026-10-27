module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def f4SignRepsB4 : List (List Bool) :=
  [[false, false, false, false], [true, false, false, false], [false, false, false, true]]

@[expose] def f4SignOrbitB4 : List (List Bool × ℕ × List ℕ) :=
  [([false, false, false, false], 0, []), ([true, false, false, false], 1, []),
    ([true, true, false, false], 1, [0]), ([false, true, true, false], 1, [1, 0]),
    ([false, true, true, true], 1, [2, 1, 0]), ([true, true, false, true], 1, [1, 2, 1, 0]),
    ([false, true, false, true], 1, [3, 2, 1, 0]),
    ([true, false, false, true], 1, [0, 1, 2, 1, 0]),
    ([true, true, true, true], 1, [3, 1, 2, 1, 0]),
    ([true, false, true, true], 1, [3, 0, 1, 2, 1, 0]),
    ([true, true, true, false], 1, [2, 3, 1, 2, 1, 0]),
    ([true, false, true, false], 1, [2, 3, 0, 1, 2, 1, 0]),
    ([false, true, false, false], 1, [1, 2, 3, 1, 2, 1, 0]),
    ([false, false, false, true], 2, []), ([false, false, true, true], 2, [3]),
    ([false, false, true, false], 2, [2, 3])]

theorem f4SignOrbitB4_check : OrbitCheck .F4 f4SignRepsB4 f4SignOrbitB4 := by
  unfold OrbitCheck
  decide +kernel

end CFSG.ComponentClassification.CatLeafProof
