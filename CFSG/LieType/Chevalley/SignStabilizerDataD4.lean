module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def d4SignReps : List (List Bool) :=
  [[false, false, false, false], [true, false, false, false], [false, true, false, false], [true,
    true, false, false], [false, false, true, false]]

@[expose] def d4SignOrbit : List (List Bool × ℕ × List ℕ) :=
  [([false, false, false, false], 0, []), ([true, false, false, false], 1, []), ([true, false, true,
    false], 1, [0]), ([false, true, true, true], 1, [2, 0]), ([false, true, false, true], 1, [1, 2,
    0]), ([false, true, false, false], 2, []), ([false, true, true, false], 2, [1]), ([true, false,
    true, true], 2, [2, 1]), ([true, false, false, true], 2, [0, 2, 1]), ([true, true, false,
    false], 3, []), ([true, true, true, false], 3, [0]), ([false, false, true, true], 3, [2, 0]),
    ([false, false, false, true], 3, [3, 2, 0]), ([false, false, true, false], 4, []), ([true, true,
    true, true], 4, [2]), ([true, true, false, true], 4, [0, 2])]

@[expose] def d4SignStab0
    : StabCert where
  mask := [false, false, false, false]
  simple := [0, 1, 2, 3]
  elems :=
    [[0, 1, 2, 3]]

@[expose] def d4SignStab1
    : StabCert where
  mask := [true, false, false, false]
  simple := [1, 2, 3]
  elems :=
    [[0, 1, 2, 3], [4, 1, 5, 3], [11, 7, 0, 9], [17, 2, 0, 15], [18, 15, 0, 2], [21, 9, 0, 7], [23,
      3, 5, 1], [23, 3, 2, 1]]

@[expose] def d4SignStab2
    : StabCert where
  mask := [false, true, false, false]
  simple := [0, 2, 3]
  elems :=
    [[0, 1, 2, 3], [0, 6, 7, 3], [5, 14, 1, 9], [2, 17, 1, 13], [13, 20, 1, 2], [9, 21, 1, 5], [3,
      23, 7, 0], [3, 23, 2, 0]]

@[expose] def d4SignStab3
    : StabCert where
  mask := [true, true, false, false]
  simple := [2, 3, 12]
  elems :=
    [[0, 1, 2, 3], [4, 1, 5, 3], [0, 6, 7, 3], [4, 6, 12, 3], [11, 7, 0, 9], [5, 14, 1, 9], [18, 15,
      0, 2], [13, 20, 1, 2]]

@[expose] def d4SignStab4
    : StabCert where
  mask := [false, false, true, false]
  simple := [0, 1, 3, 22]
  elems :=
    [[0, 1, 2, 3], [5, 7, 8, 9], [2, 12, 11, 13], [12, 2, 14, 15], [13, 15, 16, 2], [7, 5, 17, 19],
      [9, 19, 18, 5], [19, 9, 20, 7], [1, 0, 17, 22], [15, 13, 21, 12], [3, 22, 18, 0], [22, 3, 20,
      1]]

theorem d4SignOrbit_check : OrbitCheck .D4 d4SignReps d4SignOrbit := by
  unfold OrbitCheck
  decide +kernel

theorem d4SignStab0_check
    : d4SignStab0.check d4Certificate = true := by
  decide +kernel

theorem d4SignStab0_passing
    : (d4SignStab0.passing d4Certificate).length ≤ 4 := by
  decide +kernel

theorem d4SignStab0_elemAb
    : d4SignStab0.checkElemAb d4Certificate = true := by
  decide +kernel

theorem d4SignStab1_check
    : d4SignStab1.check d4Certificate = true := by
  decide +kernel

theorem d4SignStab1_passing
    : (d4SignStab1.passing d4Certificate).length ≤ 4 := by
  decide +kernel

theorem d4SignStab1_elemAb
    : d4SignStab1.checkElemAb d4Certificate = true := by
  decide +kernel

theorem d4SignStab2_check
    : d4SignStab2.check d4Certificate = true := by
  decide +kernel

theorem d4SignStab2_passing
    : (d4SignStab2.passing d4Certificate).length ≤ 4 := by
  decide +kernel

theorem d4SignStab2_elemAb
    : d4SignStab2.checkElemAb d4Certificate = true := by
  decide +kernel

theorem d4SignStab3_check
    : d4SignStab3.check d4Certificate = true := by
  decide +kernel

theorem d4SignStab3_passing
    : (d4SignStab3.passing d4Certificate).length ≤ 4 := by
  decide +kernel

theorem d4SignStab3_elemAb
    : d4SignStab3.checkElemAb d4Certificate = true := by
  decide +kernel

theorem d4SignStab4_check
    : d4SignStab4.check d4Certificate = true := by
  decide +kernel

theorem d4SignStab4_passing
    : (d4SignStab4.passing d4Certificate).length ≤ 4 := by
  decide +kernel

theorem d4SignStab4_elemAb
    : d4SignStab4.checkElemAb d4Certificate = true := by
  decide +kernel

theorem card_kernelPosStabilizer_le_D4
    : ∀ ρ < d4SignReps.length,
    Nat.card (kernelPosStabilizer (maskChar (τ := .D4) (listMask (d4SignReps.getD ρ [])))) ≤ 4 := by
  intro ρ hρ
  have hlen : d4SignReps.length = 5 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact (StabCert.card_kernelPosStabilizer_le d4Certificate_check d4SignStab0_check).trans
      d4SignStab0_passing
  · exact (StabCert.card_kernelPosStabilizer_le d4Certificate_check d4SignStab1_check).trans
      d4SignStab1_passing
  · exact (StabCert.card_kernelPosStabilizer_le d4Certificate_check d4SignStab2_check).trans
      d4SignStab2_passing
  · exact (StabCert.card_kernelPosStabilizer_le d4Certificate_check d4SignStab3_check).trans
      d4SignStab3_passing
  · exact (StabCert.card_kernelPosStabilizer_le d4Certificate_check d4SignStab4_check).trans
      d4SignStab4_passing

theorem kernelPosStabilizer_comm_sq_D4
    : ∀ ρ < d4SignReps.length, ∀ ω ω' : WeylGroup .D4,
    ω ∈ kernelPosStabilizer (maskChar (listMask (d4SignReps.getD ρ []))) →
    ω' ∈ kernelPosStabilizer (maskChar (listMask (d4SignReps.getD ρ []))) →
      ω * ω' = ω' * ω ∧ ω * ω = 1 := by
  intro ρ hρ ω ω' hω hω'
  have hlen : d4SignReps.length = 5 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact StabCert.kernelPosStabilizer_comm_sq d4Certificate_check d4SignStab0_check
      d4SignStab0_elemAb hω hω'
  · exact StabCert.kernelPosStabilizer_comm_sq d4Certificate_check d4SignStab1_check
      d4SignStab1_elemAb hω hω'
  · exact StabCert.kernelPosStabilizer_comm_sq d4Certificate_check d4SignStab2_check
      d4SignStab2_elemAb hω hω'
  · exact StabCert.kernelPosStabilizer_comm_sq d4Certificate_check d4SignStab3_check
      d4SignStab3_elemAb hω hω'
  · exact StabCert.kernelPosStabilizer_comm_sq d4Certificate_check d4SignStab4_check
      d4SignStab4_elemAb hω hω'

end CFSG.LieType.Chevalley
