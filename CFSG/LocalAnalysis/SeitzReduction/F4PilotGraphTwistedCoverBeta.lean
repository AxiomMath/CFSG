module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedCoverSurj
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedDModel

public section

namespace CFSG.SeitzReduction.F4Pilot

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer descentField
  mem_descentField)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup sigma)
open CFSG.LieType.Steinberg.Isogeny (e6IsogenyT e6IsogenyT_sigma)
open CFSG.LieType.Steinberg.Minuscule

section Swap

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (ω : F)

theorem d4Swap_d4Iota (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    TwistedE6Pilot.d4Swap F (d4Iota σ ω v) = d4Iota σ ω (minusShearMat (d4MinusB hσσ ω) *ᵥ v) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hu : ((minusShearMat (d4MinusB hσσ ω) *ᵥ v) (Sum.inr (Sum.inr 0)) : F) =
      (v (Sum.inr (Sum.inr 0)) : F) + (ω + σ ω) * (v (Sum.inr (Sum.inr 1)) : F) := by
    rw [minusShearMat_mulVec_u]
    rfl
  have hw : (minusShearMat (d4MinusB hσσ ω) *ᵥ v) (Sum.inr (Sum.inr 1)) =
      v (Sum.inr (Sum.inr 1)) := minusShearMat_mulVec_apply_of_ne _ _ w_ne_u
  funext s
  rcases s with j | j
  · rw [TwistedE6Pilot.d4Swap_apply]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [swap43_inl_of_lt hj, d4Iota_apply, d4Iota_apply, d4IotaFun, d4IotaFun,
        dite_eq_left hj, dite_eq_left hj,
        minusShearMat_mulVec_apply_of_ne _ _ (Sum.inl_ne_inr)]
    · obtain rfl := eq_three_of_not_lt hj
      rw [Equiv.swap_apply_left, d4Iota_apply, d4Iota_apply, d4IotaFun, d4IotaFun,
        dite_eq_right hj, dite_eq_right hj, hu, hw]
      linear_combination (-(v (Sum.inr (Sum.inr 1)) : F) * ω) * h2
  · rw [TwistedE6Pilot.d4Swap_apply]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [swap43_inr_of_lt hj, d4Iota_apply, d4Iota_apply, d4IotaFun, d4IotaFun,
        dite_eq_left hj, dite_eq_left hj,
        minusShearMat_mulVec_apply_of_ne _ _ (fun h => Sum.inl_ne_inr (Sum.inr_injective h))]
    · obtain rfl := eq_three_of_not_lt hj
      rw [Equiv.swap_apply_right, d4Iota_apply, d4Iota_apply, d4IotaFun, d4IotaFun,
        dite_eq_right hj, dite_eq_right hj, hu, hw]
      linear_combination (-(v (Sum.inr (Sum.inr 1)) : F) * σ ω) * h2

end Swap

section Sigma


variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

omit [CharP F 2] in
theorem e6IsogenyM_sigma_id (g : e6Data_valid.minGroup F) :
    e6IsogenyM F (sigma F (RingHom.id F) g) =
      twistHom TwistTag.E6 F (RingHom.id F) (e6IsogenyM F g) := by
  change ((e6IsogenyT F (sigma F (RingHom.id F) g) : adjointGroup TwistTag.E6.tag F) :
    ModGL TwistTag.E6.tag F) = _
  rw [e6IsogenyT_sigma (RingHom.id F) g, coe_twistC]
  rfl

include hω in
theorem twCoverPhi_sigmaHat {x y : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    (hxy : (y : fixedGroup F (σ : F →+* F)) = sigmaHat (σ : F →+* F) x) :
    (twCoverPhi σ hσσ hω y).val =
      toLinEquiv _ (descentField σ) (minusShear (d4MinusB hσσ ω)) *
        (twCoverPhi σ hσσ hω x).val *
          (toLinEquiv _ (descentField σ) (minusShear (d4MinusB hσσ ω)))⁻¹ := by
  set g : d4Levi F := ⟨e6IsogenyM F ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F),
    (twCoverIsog F (σ : F →+* F) x).2.1⟩ with hg
  have hφy : e6IsogenyM F ((y : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      ((d4Frob (RingHom.id F) g : d4Levi F) : ModGL Tag.E6 F) := by
    rw [hxy, coe_sigmaHat, e6IsogenyM_sigma_id, coe_d4Frob]
    rfl
  have hψy := d4FixedPsi_twCoverIsog hσσ hφy
  have hψx := d4FixedPsi_twCoverIsog hσσ (x := x) (h := g) rfl
  have hτ : ∀ w : Fin 4 ⊕ Fin 4 → F, d4Tau (RingEquiv.refl F) w = TwistedE6Pilot.d4Swap F w :=
    fun w => funext fun s => rfl
  have hss : ∀ w : Fin 4 ⊕ Fin 4 → F,
      TwistedE6Pilot.d4Swap F (TwistedE6Pilot.d4Swap F w) = w :=
    fun w => funext fun s => by simp [TwistedE6Pilot.d4Swap_apply]
  refine LinearEquiv.ext fun v => d4Iota_injective hω ?_
  have hψ := d4Psi_d4Frob_d4Tau (RingEquiv.refl F) g (TwistedE6Pilot.d4Swap F (d4Iota σ ω v))
  rw [hτ, hss, hτ] at hψ
  have hinv : (((minusShear (d4MinusB hσσ ω))⁻¹ : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (descentField σ)) : Matrix _ _ (descentField σ)) = minusShearMat (d4MinusB hσσ ω) :=
    coe_minusShear_inv _
  have hmat : ((minusShear (d4MinusB hσσ ω) : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (descentField σ)) : Matrix _ _ (descentField σ)) = minusShearMat (d4MinusB hσσ ω) := rfl
  rw [coe_twCoverPhi, d4Iota_d4DescentEquiv, hψy]
  change d4Psi F (d4Frob ((RingEquiv.refl F) : F →+* F) g) (d4Iota σ ω v) = _
  rw [hψ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← map_inv, toLinEquiv_apply,
    toLinEquiv_apply, hinv, hmat, ← d4Swap_d4Iota hσσ ω, coe_twCoverPhi, d4Iota_d4DescentEquiv,
    hψx, ← d4Swap_d4Iota hσσ ω]

end Sigma

section Stated

variable (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
  (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def elementaryMinusOmegaEquiv :
    elementaryGroup (quadMinus 4 k b c) ≃* StatedOmega (StatedQuadMinus 4 k b c) :=
  ((elementaryGroup (quadMinus 4 k b c)).equivMapOfInjective
      (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).symm.toMonoidHom
      (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).symm.injective).trans
    (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map
      (n := 4) (K := k) (by norm_num) hirr).symm)

omit [CharP k 2] in
theorem coe_elementaryMinusOmegaEquiv (g : elementaryGroup (quadMinus 4 k b c)) :
    ((elementaryMinusOmegaEquiv k hirr g : StatedOmega (StatedQuadMinus 4 k b c)) :
      GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) =
        (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).symm g.val :=
  rfl

theorem elementaryMinusOmegaEquiv_conj {g g' : elementaryGroup (quadMinus 4 k b c)}
    (h : g'.val = toLinEquiv _ k (minusShear b) * g.val * (toLinEquiv _ k (minusShear b))⁻¹) :
    elementaryMinusOmegaEquiv k hirr g' =
      omegaMinusBetaC k b c (elementaryMinusOmegaEquiv k hirr g) := by
  apply Subtype.ext
  rw [coe_omegaMinusBetaC, coe_elementaryMinusOmegaEquiv, coe_elementaryMinusOmegaEquiv, h,
    map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end Stated

section Cover


variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

variable (σ) in
@[expose] noncomputable def twCoverPi :
    twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes →*
      StatedOmega (StatedQuadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) :=
  (elementaryMinusOmegaEquiv (descentField σ) (d4Minus_irr hσσ hω)).toMonoidHom.comp
    (twCoverPhi σ hσσ hω)

include hω in
theorem twCoverPi_surjective : Function.Surjective (twCoverPi σ hσσ hω) :=
  (elementaryMinusOmegaEquiv (descentField σ) (d4Minus_irr hσσ hω)).surjective.comp
    ((d4FixedEquiv hσσ hω).surjective.comp (twCoverIsog_surjective hσσ hω))

theorem ker_twCoverPi_le_center :
    (twCoverPi σ hσσ hω).ker ≤
      Subgroup.center (twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes) := by
  intro x hx
  apply ker_twCoverIsog_le_center
  rw [MonoidHom.mem_ker] at hx ⊢
  apply (d4FixedEquiv hσσ hω).injective
  apply (elementaryMinusOmegaEquiv (descentField σ) (d4Minus_irr hσσ hω)).injective
  rw [map_one, map_one]
  exact hx

theorem twCoverPi_sigmaHat {x y : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    (hxy : (y : fixedGroup F (σ : F →+* F)) = sigmaHat (σ : F →+* F) x) :
    twCoverPi σ hσσ hω y =
      omegaMinusBetaC (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) (twCoverPi σ hσσ hω x) :=
  elementaryMinusOmegaEquiv_conj _ (d4Minus_irr hσσ hω) (twCoverPhi_sigmaHat hσσ hω hxy)

end Cover

end CFSG.SeitzReduction.F4Pilot
