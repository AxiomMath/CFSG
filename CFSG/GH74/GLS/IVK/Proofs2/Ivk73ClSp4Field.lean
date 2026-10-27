module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSp
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Module Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.RestrictedStd
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.ComponentClassification.OddClassSelector CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem psp4_field_false {A : Type} [Group A] {K : Subgroup A} {ℓ e : ℕ} {F : Type} [Field F]
    [Finite F] (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = ℓ ^ e)
    (hs : SmallSource K) {ρ : A →* MulAut (StatedProj (StatedSp 2 F))}
    (hinj : Function.Injective ρ)
    (hcj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))))
    {u : A}
    (hL₁ : CFSG.Assembly.IsComponentOf (K.map ρ)
      (inner (StatedProj (StatedSp 2 F)) ⊓ centralizer {ρ u}))
    {Am : gsp 2 F} {τσ : F ≃+* F} (hα : ρ u = conjAut 2 F Am * fieldAut 2 F τσ)
    (hσ2 : τσ ^ 2 = 1) {dd : Fˣ}
    (hdd : (Am : GL (Fin 2 ⊕ Fin 2) F) * glFieldEquiv (Fin 2 ⊕ Fin 2) τσ Am =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) dd) (hσ : τσ ≠ 1) : False := by
  classical
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hr1 : 1 ≤ 2 := by norm_num
  obtain ⟨hX, hXmap⟩ := isComponentOf_comap_conj hcj hL₁
  set X : Subgroup (StatedProj (StatedSp 2 F)) := (K.map ρ).comap MulAut.conj with hXdef
  have eLX : K ≃* X := (K.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hXmap.symm).trans
      ((X.equivMapOfInjective _ hcj).symm))
  have hsX : SmallSource X := smallSource_of_mulEquiv eLX hs
  set μ := multiplierUnit Am with hμdef
  have hμ := multiplierUnit_spec Am
  let e' := projectiveStatedEquiv (K := F) hr1
  have hBalt := SymplecticFlag.pairedSympForm_isAlt (K := F) (r := 2)
  have hBnd := SymplecticFlag.pairedSympForm_nondegenerate (K := F) (r := 2)
  have hdim := SymplecticFlag.finrank_standard (K := F) (r := 2)
  have hsX' : SmallSource (X.map e'.toMonoidHom) :=
    smallSource_of_mulEquiv (X.equivMapOfInjective _ e'.injective) hsX
  have hint : ∀ x, e' (ρ u x) = projectiveSemilinearConjugation (pairedSympForm F 2) τσ
      (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) F) τσ) μ (semilinearCoordMap_smul _ τσ)
      (semilinearCoordMap_form _ τσ μ hμ) (e' x) := by
    intro x
    rw [hα]
    exact projectiveStatedEquiv_conjAut_fieldAut hr1 Am τσ μ hμ x
  have hX' : CFSG.Assembly.IsComponentOf (X.map e'.toMonoidHom)
      (FixedCommutingProduct.fixedSubgroup (projectiveSemilinearConjugation (pairedSympForm F 2) τσ
        (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) F) τσ) μ (semilinearCoordMap_smul _ τσ)
        (semilinearCoordMap_form _ τσ μ hμ))) := by
    rw [← map_fixedSubgroup_of_comm e' _ _ hint]
    exact SymmetricLocal.isComponentOf_map_of_injective _ e'.injective hX
  have hsquare := semilinearCoordMap_sq (Am : GL (Fin 2 ⊕ Fin 2) F) τσ hσ2 dd hdd
  have hinv : ∀ x, (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) F) τσ).symm
      ((semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) F) τσ).symm x) = (dd : F)⁻¹ • x :=
    fun x => by
      rw [AddEquiv.symm_apply_eq, AddEquiv.symm_apply_eq, hsquare, smul_smul,
        mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
  have hφφ : ∀ g, semilinearConjugation (pairedSympForm F 2) τσ
      (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) F) τσ) μ (semilinearCoordMap_smul _ τσ)
        (semilinearCoordMap_form _ τσ μ hμ) (semilinearConjugation (pairedSympForm F 2) τσ
          (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) F) τσ) μ (semilinearCoordMap_smul _ τσ)
          (semilinearCoordMap_form _ τσ μ hμ) g) = g := by
    intro g
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [semilinearConjugation_apply, semilinearConjugation_apply, hinv, map_smul, hsquare,
      smul_smul, mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
  obtain ⟨Y, hY, ⟨σY, -, hσYk, -⟩, -⟩ := central_lift (scalarSigns (pairedSympForm F 2))
    (scalarSigns_central _) _ (semilinear_scalarSigns_invariant _ τσ _ μ _ _) hφφ hX'
  rw [fixed_semilinearConjugation_eq] at hY
  exact sp_field_false hℓ hℓ2 he hF (by norm_num) hdim hBalt hBnd τσ hσ2 hσ _ μ dd
    (semilinearCoordMap_smul _ τσ) (semilinearCoordMap_form _ τσ μ hμ) hsquare hY σY hσYk hsX'


end CFSG.GH74.GLS.IVK
