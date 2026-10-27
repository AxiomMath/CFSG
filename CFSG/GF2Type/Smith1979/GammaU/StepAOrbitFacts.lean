module

public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

@[expose] def saSet : Set (V12 ≃ₗ[ZMod 2] V12) := {U | ∃ r ∈ saGens, ∀ y, U y = linOfRows r y}

structure StepAOrbitFacts : Prop where
  exists_gammaU : ∀ v : V12, v ≠ 0 → q0 v = 0 → ∃ g ∈ gammaU, g (vecOf a0) = v
  saSet_spec : ∀ U ∈ saSet, U ∈ gammaU ∧ U (vecOf a0) = vecOf a0
  exists_saGens : ∀ r ∈ saGens, ∃ U : V12 ≃ₗ[ZMod 2] V12, ∀ y, U y = linOfRows r y
  exists_rep : ∀ D : Submodule (ZMod 2) V12, (∀ x ∈ D, q0 x = 0) → finrank (ZMod 2) D = 6 →
    vecOf a0 ∈ D → ∃ rep ∈ dReps, ∃ h ∈ Submonoid.closure saSet,
      D = (spanOf rep).map (h : V12 →ₗ[ZMod 2] V12)

end CFSG.GF2Type.Smith1979.GammaU.StepA

end
