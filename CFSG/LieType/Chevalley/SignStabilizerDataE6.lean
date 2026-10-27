module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def e6SignReps : List (List Bool) :=
  [[false, false, false, false, false, false], [true, false, false, false, false, false], [false,
    true, false, false, false, false]]

@[expose] def e6SignOrbit : List (List Bool × ℕ × List ℕ) :=
  [([false, false, false, false, false, false], 0, []), ([true, false, false, false, false, false],
    1, []), ([true, false, true, false, false, false], 1, [0]), ([false, false, true, true, false,
    false], 1, [2, 0]), ([false, true, false, true, true, false], 1, [3, 2, 0]), ([false, true,
    false, false, true, false], 1, [1, 3, 2, 0]), ([false, true, false, false, true, true], 1, [4,
    3, 2, 0]), ([false, true, false, true, true, true], 1, [4, 1, 3, 2, 0]), ([false, true, false,
    false, false, true], 1, [5, 4, 3, 2, 0]), ([false, false, true, true, false, true], 1, [3, 4, 1,
    3, 2, 0]), ([false, true, false, true, false, true], 1, [5, 4, 1, 3, 2, 0]), ([true, false,
    true, false, false, true], 1, [2, 3, 4, 1, 3, 2, 0]), ([false, false, true, true, true, true],
    1, [5, 3, 4, 1, 3, 2, 0]), ([true, false, false, false, false, true], 1, [0, 2, 3, 4, 1, 3, 2,
    0]), ([true, false, true, false, true, true], 1, [5, 2, 3, 4, 1, 3, 2, 0]), ([false, false,
    true, false, true, false], 1, [4, 5, 3, 4, 1, 3, 2, 0]), ([true, false, false, false, true,
    true], 1, [5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, false, true, true, true, false], 1, [4, 5, 2, 3,
    4, 1, 3, 2, 0]), ([true, false, false, true, true, false], 1, [4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, true, false, false], 1, [3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true, true,
    true, true, false, false], 1, [3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, false, false,
    false, false], 1, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true, true, true, false, false, false],
    1, [1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, false, false, false], 1, [2, 3,
    4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, true, false, false], 1, [2, 1, 3, 4, 5, 0,
    2, 3, 4, 1, 3, 2, 0]), ([false, false, false, true, true, false], 1, [3, 2, 1, 3, 4, 5, 0, 2, 3,
    4, 1, 3, 2, 0]), ([false, false, false, false, true, true], 1, [4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4,
    1, 3, 2, 0]), ([false, false, false, false, false, true], 1, [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3,
    4, 1, 3, 2, 0]), ([false, true, false, false, false, false], 2, []), ([false, true, false, true,
    false, false], 2, [1]), ([false, false, true, true, true, false], 2, [3, 1]), ([true, false,
    true, false, true, false], 2, [2, 3, 1]), ([false, false, true, false, true, true], 2, [4, 3,
    1]), ([true, false, false, false, true, false], 2, [0, 2, 3, 1]), ([true, false, true, true,
    true, true], 2, [4, 2, 3, 1]), ([false, false, true, false, false, true], 2, [5, 4, 3, 1]),
    ([true, false, false, true, true, true], 2, [4, 0, 2, 3, 1]), ([true, true, false, true, false,
    true], 2, [3, 4, 2, 3, 1]), ([true, false, true, true, false, true], 2, [5, 4, 2, 3, 1]),
    ([true, true, true, true, false, true], 2, [3, 4, 0, 2, 3, 1]), ([true, false, false, true,
    false, true], 2, [5, 4, 0, 2, 3, 1]), ([true, true, false, false, false, true], 2, [1, 3, 4, 2,
    3, 1]), ([true, true, false, true, true, true], 2, [5, 3, 4, 2, 3, 1]), ([true, true, true,
    false, false, true], 2, [1, 3, 4, 0, 2, 3, 1]), ([false, true, true, false, false, true], 2, [2,
    3, 4, 0, 2, 3, 1]), ([true, true, true, true, true, true], 2, [5, 3, 4, 0, 2, 3, 1]), ([true,
    true, false, false, true, true], 2, [5, 1, 3, 4, 2, 3, 1]), ([true, true, false, false, true,
    false], 2, [4, 5, 3, 4, 2, 3, 1]), ([false, true, true, true, false, true], 2, [2, 1, 3, 4, 0,
    2, 3, 1]), ([true, true, true, false, true, true], 2, [5, 1, 3, 4, 0, 2, 3, 1]), ([false, true,
    true, false, true, true], 2, [5, 2, 3, 4, 0, 2, 3, 1]), ([true, true, true, false, true, false],
    2, [4, 5, 3, 4, 0, 2, 3, 1]), ([true, true, false, true, true, false], 2, [4, 5, 1, 3, 4, 2, 3,
    1]), ([false, false, false, true, true, true], 2, [3, 2, 1, 3, 4, 0, 2, 3, 1]), ([false, true,
    true, true, true, true], 2, [5, 2, 1, 3, 4, 0, 2, 3, 1]), ([true, true, true, true, true,
    false], 2, [4, 5, 1, 3, 4, 0, 2, 3, 1]), ([false, true, true, true, true, false], 2, [4, 5, 2,
    3, 4, 0, 2, 3, 1]), ([true, false, true, true, false, false], 2, [3, 4, 5, 1, 3, 4, 2, 3, 1]),
    ([false, false, false, false, true, false], 2, [4, 3, 2, 1, 3, 4, 0, 2, 3, 1]), ([false, false,
    false, true, false, true], 2, [5, 3, 2, 1, 3, 4, 0, 2, 3, 1]), ([false, true, true, false, true,
    false], 2, [4, 5, 2, 1, 3, 4, 0, 2, 3, 1]), ([true, false, false, true, false, false], 2, [3, 4,
    5, 1, 3, 4, 0, 2, 3, 1]), ([false, false, false, true, false, false], 2, [3, 4, 5, 2, 3, 4, 0,
    2, 3, 1]), ([false, false, true, false, false, false], 2, [2, 3, 4, 5, 1, 3, 4, 2, 3, 1])]

@[expose] def e6SignStab0
    : StabCert where
  mask := [false, false, false, false, false, false]
  simple := [0, 1, 2, 3, 4, 5]
  elems :=
    [[0, 1, 2, 3, 4, 5]]

@[expose] def e6SignStab1
    : StabCert where
  mask := [true, false, false, false, false, false]
  simple := [1, 2, 3, 4, 5]
  elems :=
    [[0, 1, 2, 3, 4, 5], [6, 1, 7, 3, 4, 5], [17, 1, 0, 11, 4, 5], [27, 9, 0, 2, 13, 5], [37, 3, 0,
      2, 21, 5], [38, 21, 0, 2, 3, 15], [46, 13, 0, 2, 9, 15], [47, 33, 0, 2, 3, 4], [53, 4, 0, 11,
      1, 25], [54, 25, 0, 2, 9, 4], [59, 4, 7, 3, 1, 35], [60, 15, 0, 11, 1, 13], [59, 4, 2, 3, 1,
      40], [64, 15, 7, 3, 1, 23], [65, 5, 0, 23, 1, 3], [64, 15, 2, 3, 1, 29], [67, 5, 7, 13, 1,
      11], [67, 5, 2, 13, 1, 18], [69, 5, 18, 4, 9, 2], [69, 5, 11, 4, 9, 7], [71, 5, 28, 4, 3, 2],
      [71, 5, 20, 4, 3, 7], [69, 5, 3, 4, 20, 0], [71, 5, 9, 4, 11, 0], [71, 5, 1, 13, 2, 0], [71,
      15, 1, 3, 2, 0], [71, 4, 1, 3, 2, 0]]

@[expose] def e6SignStab2
    : StabCert where
  mask := [false, true, false, false, false, false]
  simple := [0, 2, 3, 4, 5, 70]
  elems :=
    [[0, 1, 2, 3, 4, 5], [0, 8, 2, 9, 4, 5], [0, 19, 11, 1, 13, 5], [7, 30, 3, 1, 23, 5], [0, 31,
      23, 1, 3, 15], [2, 37, 3, 1, 29, 5], [7, 41, 13, 1, 11, 15], [0, 42, 35, 1, 3, 4], [2, 46, 13,
      1, 18, 15], [18, 50, 4, 9, 2, 25], [7, 51, 25, 1, 11, 4], [11, 53, 4, 9, 7, 25], [2, 54, 25,
      1, 18, 4], [28, 50, 4, 3, 2, 33], [18, 57, 15, 9, 2, 13], [20, 53, 4, 3, 7, 33], [3, 59, 4,
      20, 0, 35], [11, 60, 15, 9, 7, 13], [28, 57, 15, 3, 2, 21], [29, 63, 5, 21, 2, 3], [9, 59, 4,
      11, 0, 44], [20, 60, 15, 3, 7, 21], [3, 64, 15, 20, 0, 23], [23, 65, 5, 21, 7, 3], [39, 63, 5,
      13, 2, 9], [1, 59, 13, 2, 0, 52], [9, 64, 15, 11, 0, 32], [32, 65, 5, 13, 7, 9], [13, 67, 5,
      32, 0, 11], [48, 63, 5, 4, 11, 1], [1, 59, 3, 2, 0, 58], [1, 64, 25, 2, 0, 43], [21, 67, 5,
      23, 0, 20], [43, 65, 5, 4, 18, 1], [4, 69, 5, 43, 0, 2], [55, 63, 5, 4, 3, 1]]

theorem e6SignOrbit_check : OrbitCheck .E6 e6SignReps e6SignOrbit := by
  unfold OrbitCheck
  decide +kernel

theorem e6SignStab0_check
    : e6SignStab0.check e6Certificate = true := by
  decide +kernel

theorem e6SignStab0_passing
    : (e6SignStab0.passing e6Certificate).length ≤ 1 := by
  decide +kernel

theorem e6SignStab1_check
    : e6SignStab1.check e6Certificate = true := by
  decide +kernel

theorem e6SignStab1_passing
    : (e6SignStab1.passing e6Certificate).length ≤ 1 := by
  decide +kernel

theorem e6SignStab2_check
    : e6SignStab2.check e6Certificate = true := by
  decide +kernel

theorem e6SignStab2_passing
    : (e6SignStab2.passing e6Certificate).length ≤ 1 := by
  decide +kernel

theorem card_kernelPosStabilizer_le_E6
    : ∀ ρ < e6SignReps.length,
    Nat.card (kernelPosStabilizer (maskChar (τ := .E6) (listMask (e6SignReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : e6SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact (StabCert.card_kernelPosStabilizer_le e6Certificate_check e6SignStab0_check).trans
      e6SignStab0_passing
  · exact (StabCert.card_kernelPosStabilizer_le e6Certificate_check e6SignStab1_check).trans
      e6SignStab1_passing
  · exact (StabCert.card_kernelPosStabilizer_le e6Certificate_check e6SignStab2_check).trans
      e6SignStab2_passing

end CFSG.LieType.Chevalley
