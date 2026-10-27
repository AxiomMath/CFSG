module

public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

@[expose] def FrameGood (i c : ℕ) (W : V12 ≃ₗ[ZMod 2] V12) : Prop :=
  (W (vecOf a0) = vecOf a0 ∧ ∀ l, RowsSet (compOf i) l ↔ RowsSet (compOf c) (W⁻¹ * l * W)) ∨
    ∀ F : Subgroup (V12 ≃ₗ[ZMod 2] V12), (∀ l, l ∈ F ↔ RowsSet (compOf c) (W⁻¹ * l * W)) →
      Viol.Violation (ResPair.n2 i ⊔ F) (compOf i) (idR :: ResPair.hyp10 i)

@[expose] def FrameCensusFacts (i : ℕ) : Prop :=
  ∃ T m, FrameTr T m ∧ ∃ P : List (V12 ≃ₗ[ZMod 2] V12), (∀ g ∈ P, g ∈ gammaU) ∧
    ResPair.n2 i ≤ gammaU ∧
    (∀ x, x ≠ 0 → q0 x = 0 → ∃ g ∈ P, ∃ U ∈ ResPair.n2 i, x = U (g (vecOf a0))) ∧
    ∀ g ∈ P, ∀ j < m, ∃ M ∈ ResPair.n2 i, M (g (vecOf a0)) = g (vecOf a0) ∧ ∃ j' < m,
      (spanOf d0).map ((g * T j : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) =
        ((spanOf d0).map ((g * T j' : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12)).map
          (M : V12 →ₗ[ZMod 2] V12) ∧
      ∀ c < 32, FrameGood i c (g * T j')

end CFSG.GF2Type.Smith1979.GammaU.StepA

end
