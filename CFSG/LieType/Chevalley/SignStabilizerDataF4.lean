module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def f4SignReps : List (List Bool) :=
  [[false, false, false, false], [true, false, false, false], [false, false, true, false]]

@[expose] def f4SignOrbit : List (List Bool × ℕ × List ℕ) :=
  [([false, false, false, false], 0, []), ([true, false, false, false], 1, []), ([true, true, false,
    false], 1, [0]), ([false, true, true, false], 1, [1, 0]), ([false, true, true, true], 1, [2, 1,
    0]), ([true, true, false, true], 1, [1, 2, 1, 0]), ([false, true, false, true], 1, [3, 2, 1,
    0]), ([true, false, false, true], 1, [0, 1, 2, 1, 0]), ([true, true, true, true], 1, [3, 1, 2,
    1, 0]), ([true, false, true, true], 1, [3, 0, 1, 2, 1, 0]), ([true, true, true, false], 1, [2,
    3, 1, 2, 1, 0]), ([true, false, true, false], 1, [2, 3, 0, 1, 2, 1, 0]), ([false, true, false,
    false], 1, [1, 2, 3, 1, 2, 1, 0]), ([false, false, true, false], 2, []), ([false, false, true,
    true], 2, [2]), ([false, false, false, true], 2, [3, 2])]

@[expose] def f4SignStab0
    : StabCert where
  mask := [false, false, false, false]
  simple := [0, 1, 2, 3]
  elems :=
    [[0, 1, 2, 3]]

@[expose] def f4SignStab1
    : StabCert where
  mask := [true, false, false, false]
  simple := [1, 2, 3, 43]
  elems :=
    [[0, 1, 2, 3], [4, 5, 2, 3], [12, 0, 8, 3], [20, 0, 8, 10], [28, 5, 2, 17], [29, 0, 17, 2], [28,
      1, 2, 24], [34, 5, 10, 8], [34, 1, 10, 16], [38, 13, 3, 8], [38, 7, 3, 16], [42, 21, 3, 2]]

@[expose] def f4SignStab2
    : StabCert where
  mask := [false, false, true, false]
  simple := [0, 1, 3, 7]
  elems :=
    [[0, 1, 2, 3], [0, 7, 9, 10], [0, 15, 19, 2]]

theorem f4SignOrbit_check : OrbitCheck .F4 f4SignReps f4SignOrbit := by
  unfold OrbitCheck
  decide +kernel

theorem f4SignStab0_check
    : f4SignStab0.check f4Certificate = true := by
  decide +kernel

theorem f4SignStab0_passing
    : (f4SignStab0.passing f4Certificate).length ≤ 1 := by
  decide +kernel

theorem f4SignStab1_check
    : f4SignStab1.check f4Certificate = true := by
  decide +kernel

theorem f4SignStab1_passing
    : (f4SignStab1.passing f4Certificate).length ≤ 1 := by
  decide +kernel

theorem f4SignStab2_check
    : f4SignStab2.check f4Certificate = true := by
  decide +kernel

theorem f4SignStab2_passing
    : (f4SignStab2.passing f4Certificate).length ≤ 1 := by
  decide +kernel

theorem card_kernelPosStabilizer_le_F4
    : ∀ ρ < f4SignReps.length,
    Nat.card (kernelPosStabilizer (maskChar (τ := .F4) (listMask (f4SignReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : f4SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact (StabCert.card_kernelPosStabilizer_le f4Certificate_check f4SignStab0_check).trans
      f4SignStab0_passing
  · exact (StabCert.card_kernelPosStabilizer_le f4Certificate_check f4SignStab1_check).trans
      f4SignStab1_passing
  · exact (StabCert.card_kernelPosStabilizer_le f4Certificate_check f4SignStab2_check).trans
      f4SignStab2_passing

end CFSG.LieType.Chevalley
