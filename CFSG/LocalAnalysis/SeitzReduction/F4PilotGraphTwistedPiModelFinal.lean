module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPiModelMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelFinal

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

local instance f4PilotGraphTwistedPiModelFinalNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Holds

theorem exists_twistedLeviPiModel {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : UnitaryFieldData 2 f F) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (ε : h.fixedField ≃+* K) :
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
        sp6ToSL6 sA ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := h.fixedField)
          lin6BlockA →
        ((Θ (omegaMinusIota hK hf hc sD) :
          twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
            fixedGroup F h.barEquiv.toRingHom) =
          ((twParamEquiv h (uEmbed6 h sA) :
            twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
              fixedGroup F h.barEquiv.toRingHom) →
        ((c3LeviEquiv K (statedSpCongr ε 3 sA) : C3Levi K) : adjointGroup .F4 K) =
          graphAutF4 K (c3LeviEquiv K (statedSpCongr ε' 3 (s₀ * sD * s₀⁻¹)) : C3Levi K)) ∧
      (∃ ε' : K ≃+* K, ∀ (sA : StatedSp 3 h.fixedField) (sD : StatedSp 3 K),
        sp6ToSL6 sA ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := h.fixedField)
          lin6BlockA →
        ((Θ (omegaMinusIota hK hf hc sD) :
          twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
            fixedGroup F h.barEquiv.toRingHom) =
          ((twParamEquiv h (uEmbed6 h sA) :
            twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
              fixedGroup F h.barEquiv.toRingHom) →
        graphAutF4 K (c3LeviEquiv K (statedSpCongr ε 3 sA) : C3Levi K) =
          ((c3LeviEquiv K (statedSpCongr ε' 3 (s₀ * sD * s₀⁻¹)) : C3Levi K) :
            adjointGroup .F4 K)) := by
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  have hω' : h.barEquiv ω ≠ ω := hω
  obtain ⟨ψ, hψ⟩ := exists_ringEquiv_sq_eq_self (K := K)
  refine ⟨_, twMinus_irr h ε hω', twTheta h ε hω' hK hf, twTheta_betaC h ε hω' hK hf, 1, ?_, ?_,
    ⟨ψ, fun sA sD hsA hx => ?_⟩, ⟨RingEquiv.refl K, fun sA sD hsA hx => ?_⟩⟩
  · intro x hx a
    rw [inv_one, one_mul, mul_one, twTheta_symm_apply]
    have hd : omegaMinusIota hK hf (twMinus_irr h ε hω') (sp6Diag K (sp6ParamA K a)) =
        ⟨diagOmegaMinus K (sp6ParamA K a), diagOmegaMinus_mem _ _ _⟩ :=
      Subtype.ext (coe_omegaMinusIota_sp6Diag hK hf _ _)
    rw [hd]
    exact twPi_commute_diag_one_two h ε hω' x hx (by simp [sp6ParamA]) (by simp [sp6ParamA])
  · intro x hx p
    obtain ⟨a, b⟩ := p
    rw [inv_one, one_mul, mul_one, twTheta_symm_apply]
    have hd : omegaMinusIota hK hf (twMinus_irr h ε hω') (sp6Diag K (sp6ParamT3 K (a, b))) =
        ⟨diagOmegaMinus K (sp6ParamT3 K (a, b)), diagOmegaMinus_mem _ _ _⟩ :=
      Subtype.ext (coe_omegaMinusIota_sp6Diag hK hf _ _)
    rw [hd]
    exact twPi_commute_diag_zero h ε hω' x hx (by rw [sp6ParamT3_apply]; rfl)
  · rw [one_mul, inv_one, mul_one]
    exact (Prod.ext_iff.1 (twPi_sp4_agree h ε hω' hK hf ψ hψ hsA hx)).1
  · rw [one_mul, inv_one, mul_one, statedSpCongr_refl_apply]
    exact (Prod.ext_iff.1 (twPi_sp4_agree h ε hω' hK hf ψ hψ hsA hx)).2

theorem twistedLeviPiModelInput_holds : TwistedLeviPiModelInput := by
  intro f hf F _ _ _ h K _ _ _ _ hK ε
  exact exists_twistedLeviPiModel hf h hK ε

end Holds

section Main

theorem seitzExclusion_highF4_of_gls3_twoRows (hGLS : GLS3OddLieAutComponentsInput)
    (h2 : TwoRowsInput) : SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_piModel hGLS twistedLeviPiModelInput_holds h2

end Main

end CFSG.SeitzReduction.F4Pilot
