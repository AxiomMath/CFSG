module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpLinear
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpLift
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Field

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem sp_field_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) {r : ℕ} (hr : 2 ≤ r) (hdim : finrank K V = 2 * r)
    {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate) (τσ : K ≃+* K)
    (hσ2 : τσ ^ 2 = 1) (hσ1 : τσ ≠ 1) (τ₀ : V ≃+ V) (μ lam : Kˣ)
    (hsemi : ∀ a x, τ₀ (a • x) = τσ a • τ₀ x)
    (hform : ∀ x y, B (τ₀ x) (τ₀ y) = (μ : K) * τσ (B x y))
    (hsquare : ∀ x, τ₀ (τ₀ x) = (lam : K) • x)
    {Y : Subgroup (isometryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (semilinearSymplecticCentralizer B τ₀))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ he hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent τσ hσ2
    hσ1 h2 (by omega) B hB hnd τ₀ μ lam hsemi hform hsquare
  obtain ⟨-, -, -, -, hfin, hrank, -, hB0alt, hB0nd, -, eD, -⟩ := hall b c hb hc
  obtain ⟨hcard0, -⟩ := CatalogueBOrthogonalInvolutionRepresentation.field_involution_facts hℓ he
    hK hσ2 hσ1
  have hk₀ : Nat.card (fixedSubfield K τσ) = Nat.card {c : K // τσ c = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight (mem_fixedSubfield K τσ))
  obtain ⟨j, hj, hjcard⟩ : ∃ j, 1 ≤ j ∧ Nat.card (fixedSubfield K τσ) = ℓ ^ j := by
    have hdvd : Nat.card (fixedSubfield K τσ) ∣ ℓ ^ e := by
      rw [← hK, hcard0, hk₀]
      exact Dvd.intro_left _ (_root_.sq _).symm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
    have h2j : ℓ ^ (2 * j) = ℓ ^ e := by
      rw [pow_mul', ← hj, hk₀, ← hcard0, hK]
    have he2 : 2 * j = e := Nat.pow_right_injective hℓ.two_le h2j
    exact ⟨j, by omega, hj⟩
  have := hfin
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf (semilinearSymplecticCentralizer B τ₀) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hY.1
  exact sp_component_false hℓ hℓ2 hj hjcard _ hB0alt hB0nd (by rw [hrank]; omega) eD hY₁
    (σ.comp eY.toMonoidHom) (ker_comp_le_center eY.toMonoidHom eY.injective σ hσk) hs

end Field

theorem sp_socle_false {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hstd : CFSG.IsStandardSubgroup L) (hs : SmallSource L) {ℓ e : ℕ} (hℓ : ℓ.Prime)
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
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩⟩ := fixed_component_of_socle hCW θ hZ hLCW
  have hW := noTightWitness_of_isStandardSubgroup hinj hinn (conj_injective hZ) hstd hLX
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
  have hW' := hW.map e'
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
    obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, -⟩, hN⟩ := central_lift (scalarSigns (pairedSympForm K r))
      (scalarSigns_central _) _ (scalarSigns_invariant _ _ μ (matrix_similitude _ μ hμ)) hφφ hX'
    rw [fixed_similitudeConjugation_eq] at hY
    exact sp_linear_false hℓ hℓ2 he hK hr hdim hBalt hBnd _ dd μ hsquare
      (matrix_similitude _ μ hμ) (matrixLinIso_ne_smul_one _ (hlin rfl)) hY σY hσYs hσYk hsX'
      (hN hW')
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

theorem sp_family_false {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.IsStandardSubgroup L) (hs : SmallSource L) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n) (hM : LieModel W .PSp n p f) : False := by
  have hLCW := LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1)
    inf_le_right
  have h := statedClassicalModel_of_lieModel hM (by simp [chevalleyExceptionalTags])
    (by simp [reeTitsTags]) (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact sp_socle_false hWs hWnab hCW ha hLCW hstd hs hp hp2 hf hK hn e

end CFSG.ComponentClassification.OddClassSelector
