module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamField
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeCovers

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  coordinateFieldMap)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG SUmCatalogueClausesAt)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_minusRootFieldParam_four (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hrow : OmegaRowAt t (modelToG e (minusPairTorus (K := K) (n := 2 + 2) (by omega) b c 2))
      (modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c 2)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ ⟨0, by omega⟩
      ⟨1, by omega⟩) := by
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  have hQσ := coordinateQuadMinus_fieldMap_of_fixed (n := 2 + 1) (by omega)
    ((hσk _).1 (ι.rangeRestrictFieldEquiv b).2) ((hσk _).1 (ι.rangeRestrictFieldEquiv c).2)
  obtain ⟨π, hπs, hπk, hπt, hDE, hπD⟩ :=
    exists_normalizedCover_minus_four hset hcat hKc hq hirr e htC ht 2 hrow ι hσ hfix
  let N : MinusNormalizedCover hirr e htC ι.fieldRange ι.rangeRestrictFieldEquiv σ hQσ :=
    ⟨π, hπs, hπk, hπt hQσ, hDE, hπD⟩
  exact N.nonempty_minusRootFieldParam ι (fun x => RingHom.rangeRestrictFieldEquiv_apply_coe ι x)
    hq hFK

theorem omegaMinusFourRootParamInput_of_catalogue (hcat : SUmCatalogueClausesAt 4) :
    OmegaMinusFourRootParamInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow F _ _ _ ι σ hσ hfix
  exact nonempty_minusRootFieldParam_four hset hcat hKc
    ((LinearPilot.four_le_card_iff_two_le hKc).2 hf2) hirr e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht (hrow 2) ι hσ hfix

theorem omegaMinusFourInput_of_catalogue_six (hswap : OmegaMinusFourSwapRowInput)
    (huniq : OmegaMinusFourUniqueInput) (hend : OmegaMinusFourEndInput)
    (hcatU : SUmCatalogueClausesAt 4) (hcatL : LinearPilot.SLmCatalogueClausesAt 4)
    (hrowA : OmegaMinusFourAnisoRowInput) : OmegaMinusFourInput :=
  omegaMinusFourInput_of_catalogue hswap (omegaMinusFourRootParamInput_of_catalogue hcatU) huniq
    hend hcatU hcatL hrowA

end Main

end CFSG.SeitzReduction.OmegaPilot
