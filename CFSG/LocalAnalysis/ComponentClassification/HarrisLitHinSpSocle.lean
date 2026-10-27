module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSpLin
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSocle
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinUniq

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open LinearMap (BilinForm)
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem sp_socle_false_of_noComm {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hU : NoCommQS (W ⊓ centralizer {a}) L) (hs : SmallSource L) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ e)
    {r : ℕ} (hr : 3 ≤ r) (θ : W ≃* StatedProj (StatedSp r K)) : False := by
  classical
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ he hK
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hr1 : 1 ≤ r := by omega
  have : IsSimpleGroup (StatedProj (StatedSp r K)) := θ.symm.isSimpleGroup
  have hnab : ∃ x y : StatedProj (StatedSp r K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnab
    refine ⟨θ x, θ y, fun h => hxy (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩, hUP⟩ :=
    fixed_component_of_socle_noComm hCW θ hZ hLCW hU
  have hαα : ρ a * ρ a = 1 := by
    rw [← map_mul, ← pow_two, ← ha, pow_orderOf_eq_one, map_one]
  have hα1 : ρ a ≠ 1 := by
    intro h
    have h1 : orderOf (ρ a) = orderOf a := orderOf_injective ρ hinj a
    rw [h, orderOf_one, ha] at h1
    exact absurd h1 (by norm_num)
  have hsX : SmallSource X := smallSource_of_mulEquiv eLX hs
  obtain ⟨Am, τσ, hα, hσ2, ⟨dd, hdd⟩, hlin, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hchar (by omega : 2 ≤ r)).2.2 (ρ a)
      hαα hα1
  set μ := multiplierUnit Am with hμdef
  have hμ := multiplierUnit_spec Am
  let e' := projectiveStatedEquiv (K := K) hr1
  have hBalt := SymplecticFlag.pairedSympForm_isAlt (K := K) (r := r)
  have hBnd := SymplecticFlag.pairedSympForm_nondegenerate (K := K) (r := r)
  have hdim := SymplecticFlag.finrank_standard (K := K) (r := r)
  have hsX' : SmallSource (X.map e'.toMonoidHom) :=
    smallSource_of_mulEquiv (X.equivMapOfInjective _ e'.injective) hsX
  have hUP' := hUP.map e'.toMonoidHom e'.injective
  by_cases hσ : τσ = 1
  · subst hσ
    have hint : ∀ x, e' (ρ a x) = projectiveConjugation (pairedSympForm K r)
        (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)) μ (matrix_similitude _ μ hμ) (e' x) := by
      intro x
      rw [hα, map_one, mul_one]
      exact projectiveStatedEquiv_conjAut hr1 Am μ hμ x
    have hX' : CFSG.Assembly.IsComponentOf (X.map e'.toMonoidHom)
        (fixedSubgroup (projectiveConjugation (pairedSympForm K r)
          (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)) μ (matrix_similitude _ μ hμ))) := by
      rw [← map_fixedSubgroup_of_comm e' _ _ hint]
      exact SymmetricLocal.isComponentOf_map_of_injective _ e'.injective hX
    have hsquare : ∀ x, matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)
        (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K) x) = (dd : K) • x :=
      semilinearCoordMap_sq _ 1 hσ2 dd hdd
    have hinv : ∀ x, (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)).symm
        ((matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)).symm x) = (dd : K)⁻¹ • x := fun x => by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, hsquare, smul_smul,
        mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
    have hφφ : ∀ g, similitudeConjugation (pairedSympForm K r)
        (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)) μ (matrix_similitude _ μ hμ)
          (similitudeConjugation (pairedSympForm K r) (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K))
            μ (matrix_similitude _ μ hμ) g) = g := by
      intro g
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [similitudeConjugation_apply, similitudeConjugation_apply, hinv, map_smul, hsquare,
        smul_smul, mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
    have hU1 : NoCommQS (fixedSubgroup (projectiveConjugation (pairedSympForm K r)
        (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)) μ (matrix_similitude _ μ hμ)))
        (X.map e'.toMonoidHom) := by
      rw [← map_fixedSubgroup_of_comm e' _ _ hint]
      exact hUP'
    obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYmk⟩, -⟩ := central_lift
      (scalarSigns (pairedSympForm K r)) (scalarSigns_central _) _
      (scalarSigns_invariant _ _ μ (matrix_similitude _ μ hμ)) hφφ hX'
    have hYX : ∀ x ∈ X.map e'.toMonoidHom, ∃ y ∈ Y,
        QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) y = x := by
      intro x hx
      obtain ⟨y, hy⟩ := hσYs ⟨x, hx⟩
      refine ⟨y, y.2, ?_⟩
      rw [← hσYmk y, hy]
    have hfixeq := fixed_similitudeConjugation_eq (pairedSympForm K r)
      (matrixLinIso (Am : GL (Fin r ⊕ Fin r) K)) μ (matrix_similitude _ μ hμ)
    rw [hfixeq] at hY
    refine sp_linear_false_of_noComm hℓ hℓ2 he hK hr hdim hBalt hBnd _ dd μ hsquare
      (matrix_similitude _ μ hμ) (matrixLinIso_ne_smul_one _ (hlin rfl)) hY σY hσYs hσYk hsX'
      (fun N hN hnorm hq hNZ h2 hcomm => ?_)
    rw [← hfixeq] at hN hnorm
    exact false_of_noCommQS_lift (scalarSigns (pairedSympForm K r)) (scalarSigns_central _) _
      (scalarSigns_invariant _ _ μ (matrix_similitude _ μ hμ)) hU1 hYX hN hnorm hq hNZ h2 hcomm
  · have hint : ∀ x, e' (ρ a x) = projectiveSemilinearConjugation (pairedSympForm K r) τσ
        (semilinearCoordMap (Am : GL (Fin r ⊕ Fin r) K) τσ) μ (semilinearCoordMap_smul _ τσ)
        (semilinearCoordMap_form _ τσ μ hμ) (e' x) := by
      intro x
      rw [hα]
      exact projectiveStatedEquiv_conjAut_fieldAut hr1 Am τσ μ hμ x
    have hX' : CFSG.Assembly.IsComponentOf (X.map e'.toMonoidHom)
        (fixedSubgroup (projectiveSemilinearConjugation (pairedSympForm K r) τσ
          (semilinearCoordMap (Am : GL (Fin r ⊕ Fin r) K) τσ) μ (semilinearCoordMap_smul _ τσ)
          (semilinearCoordMap_form _ τσ μ hμ))) := by
      rw [← map_fixedSubgroup_of_comm e' _ _ hint]
      exact SymmetricLocal.isComponentOf_map_of_injective _ e'.injective hX
    have hsquare := semilinearCoordMap_sq (Am : GL (Fin r ⊕ Fin r) K) τσ hσ2 dd hdd
    have hinv : ∀ x, (semilinearCoordMap (Am : GL (Fin r ⊕ Fin r) K) τσ).symm
        ((semilinearCoordMap (Am : GL (Fin r ⊕ Fin r) K) τσ).symm x) = (dd : K)⁻¹ • x :=
      fun x => by
        rw [AddEquiv.symm_apply_eq, AddEquiv.symm_apply_eq, hsquare, smul_smul,
          mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
    have hφφ : ∀ g, semilinearConjugation (pairedSympForm K r) τσ
        (semilinearCoordMap (Am : GL (Fin r ⊕ Fin r) K) τσ) μ (semilinearCoordMap_smul _ τσ)
          (semilinearCoordMap_form _ τσ μ hμ) (semilinearConjugation (pairedSympForm K r) τσ
            (semilinearCoordMap (Am : GL (Fin r ⊕ Fin r) K) τσ) μ (semilinearCoordMap_smul _ τσ)
            (semilinearCoordMap_form _ τσ μ hμ) g) = g := by
      intro g
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [semilinearConjugation_apply, semilinearConjugation_apply, hinv, map_smul, hsquare,
        smul_smul, mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
    obtain ⟨Y, hY, ⟨σY, -, hσYk, -⟩, -⟩ := central_lift (scalarSigns (pairedSympForm K r))
      (scalarSigns_central _) _ (semilinear_scalarSigns_invariant _ τσ _ μ _ _) hφφ hX'
    rw [fixed_semilinearConjugation_eq] at hY
    exact sp_field_false hℓ hℓ2 he hK (by omega) hdim hBalt hBnd τσ hσ2 hσ _ μ dd
      (semilinearCoordMap_smul _ τσ) (semilinearCoordMap_form _ τσ μ hμ) hsquare hY σY hσYk hsX'

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

theorem false_of_psp_ge_three (hnab : ∃ a b : Y, a * b ≠ b * a) {r ℓ e : ℕ} (hr : 3 ≤ r)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hY : StatedClassicalModel Y .PSp r ℓ e) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : False := by
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  obtain ⟨⟨-, he, -⟩, K, _, _, hK, ⟨φ₀⟩⟩ := hY
  have hcomp := isComponentOf_map_conj_layer hZ hL
  have hLCW : CFSG.Assembly.IsComponentOf
      ((GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y))
      (generalizedFitting (MulAut Y) ⊓ centralizer {τ}) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp (le_inf (hLW τ) hcomp.1)
      inf_le_right
  have hU : NoCommQS (generalizedFitting (MulAut Y) ⊓ centralizer {τ})
      ((GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y)) := by
    have h := (noCommQS_layerIn hL).map _ (conj_injective_of_center hZ)
    rwa [map_conj_fixedPoints hZ τ, ← hF] at h
  exact sp_socle_false_of_noComm hWs hWnab hWC hτ hLCW hU (smallSource_layerMap hZ hp hp2 hm h16 hL)
    hℓ hℓ2 he hK hr (eW.symm.trans φ₀)

end CFSG.ComponentClassification.HarrisLit.Hin
