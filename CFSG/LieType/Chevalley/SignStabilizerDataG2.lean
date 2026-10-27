module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def g2SignReps : List (List Bool) :=
  [[false, false], [true, false]]

@[expose] def g2SignOrbit : List (List Bool × ℕ × List ℕ) :=
  [([false, false], 0, []), ([true, false], 1, []), ([true, true], 1, [0]), ([false, true], 1, [1,
    0])]

@[expose] def g2SignStab0
    : StabCert where
  mask := [false, false]
  simple := [0, 1]
  elems :=
    [[0, 1]]

@[expose] def g2SignStab1
    : StabCert where
  mask := [true, false]
  simple := [1, 7]
  elems :=
    [[0, 1], [2, 4], [6, 8]]

theorem g2SignOrbit_check : OrbitCheck .G2 g2SignReps g2SignOrbit := by
  unfold OrbitCheck
  decide +kernel

theorem g2SignStab0_check
    : g2SignStab0.check g2Certificate = true := by
  decide +kernel

theorem g2SignStab0_passing
    : (g2SignStab0.passing g2Certificate).length ≤ 1 := by
  decide +kernel

theorem g2SignStab1_check
    : g2SignStab1.check g2Certificate = true := by
  decide +kernel

theorem g2SignStab1_passing
    : (g2SignStab1.passing g2Certificate).length ≤ 1 := by
  decide +kernel

theorem card_kernelPosStabilizer_le_G2
    : ∀ ρ < g2SignReps.length,
    Nat.card (kernelPosStabilizer (maskChar (τ := .G2) (listMask (g2SignReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : g2SignReps.length = 2 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact (StabCert.card_kernelPosStabilizer_le g2Certificate_check g2SignStab0_check).trans
      g2SignStab0_passing
  · exact (StabCert.card_kernelPosStabilizer_le g2Certificate_check g2SignStab1_check).trans
      g2SignStab1_passing

end CFSG.LieType.Chevalley
