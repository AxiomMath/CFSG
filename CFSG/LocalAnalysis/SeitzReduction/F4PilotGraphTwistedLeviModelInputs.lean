module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinTorus3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusIota

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)

local instance f4PilotGraphTwistedLeviModelInputsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Inputs


@[expose] def TwistedA3MatrixRigidityInput : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
    (θ : twLevi F h.barEquiv.toRingHom {1, 2} →* uGroup6 h),
    (∀ x, gramSUToSL h _ (θ x) ∈ blockSpecialLinear (K := F) lin6BlockA) →
    (∀ (x : twLevi F h.barEquiv.toRingHom {1, 2}) (s : StatedSp 3 h.fixedField),
      sp6ToSL6 s ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
      ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x → θ x = uEmbed6 h s) →
    (∀ x y : twLevi F h.barEquiv.toRingHom {1, 2},
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        θ y = barSU6 h (θ x)) →
    (∀ x : twLevi F h.barEquiv.toRingHom {1, 2},
      ((twParamEquiv h (θ x) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) = x) ∨
    (∀ x : twLevi F h.barEquiv.toRingHom {1, 2},
      ((twParamEquiv h (barSU6 h (θ x)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) = x)

@[expose] def TwistedLeviPiModelInput : Prop :=
  ∀ (f : ℕ) (hf : 2 ≤ f) (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
    (K : Type) [Field K] [Finite K] [CharP K 2] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ f) (ε : h.fixedField ≃+* K),
    ∃ (c : K) (hc : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0)
      (Θ : StatedOmega (StatedQuadMinus 4 K 1 c) ≃*
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes),
      (∀ g, ((Θ (omegaMinusBetaC K 1 c g) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom (Θ g)) ∧
    ∃ s₀ : StatedSp 3 K,
      (∀ x : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
        (x : fixedGroup F h.barEquiv.toRingHom) ∈ twLevi F h.barEquiv.toRingHom {1, 2} →
        ∀ a : Kˣ, Commute (Θ.symm x)
          (omegaMinusIota hK hf hc (s₀⁻¹ * sp6Diag K (sp6ParamA K a) * s₀))) ∧
      (∀ x : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes,
        (x : fixedGroup F h.barEquiv.toRingHom) ∈ twLevi F h.barEquiv.toRingHom {0} →
        ∀ p : Kˣ × Kˣ, Commute (Θ.symm x)
          (omegaMinusIota hK hf hc (s₀⁻¹ * sp6Diag K (sp6ParamT3 K p) * s₀))) ∧
      (∃ ε' : K ≃+* K, ∀ (sA : StatedSp 3 h.fixedField) (sD : StatedSp 3 K),
        sp6ToSL6 sA ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
        ((Θ (omegaMinusIota hK hf hc sD) :
          twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
            fixedGroup F h.barEquiv.toRingHom) =
          ((twParamEquiv h (uEmbed6 h sA) :
            twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
              fixedGroup F h.barEquiv.toRingHom) →
        ((c3LeviEquiv K (statedSpCongr ε 3 sA) : C3Levi K) : adjointGroup .F4 K) =
          graphAutF4 K (c3LeviEquiv K (statedSpCongr ε' 3 (s₀ * sD * s₀⁻¹)) : C3Levi K)) ∧
      (∃ ε' : K ≃+* K, ∀ (sA : StatedSp 3 h.fixedField) (sD : StatedSp 3 K),
        sp6ToSL6 sA ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA →
        ((Θ (omegaMinusIota hK hf hc sD) :
          twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
            fixedGroup F h.barEquiv.toRingHom) =
          ((twParamEquiv h (uEmbed6 h sA) :
            twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
              fixedGroup F h.barEquiv.toRingHom) →
        graphAutF4 K (c3LeviEquiv K (statedSpCongr ε 3 sA) : C3Levi K) =
          ((c3LeviEquiv K (statedSpCongr ε' 3 (s₀ * sD * s₀⁻¹)) : C3Levi K) :
            adjointGroup .F4 K))

end Inputs

end CFSG.SeitzReduction.F4Pilot
