module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusPair
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightF6Eigen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourGlobal

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt)

section Main

theorem omegaPlusFourOrthCatInput_holds :
    SLmCatalogueClausesAt 4 →
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
        ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
          (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
          (∃ hz : z ∈ CFSG.conjugate L x,
            IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
          ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹) →
        OmegaRowAt t (modelToG e (pairTorus (K := K) 0)) (modelToG e (pairPerp (K := K) 0))
          .field →
        ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
          orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
          plusNode e 0 ≤ centralizer (plusNode e 2 : Set G) ∧
            plusNode e 0 ≤ centralizer (plusNode e 3 : Set G) := by
  intro hcat G _ _ L hset f K _ _ _ hKc hf e t ht hKt hR5 hrow0 F _ _ _ ι σ hσ hfix
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hnn : ∀ k : Fin 4, ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
      (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
        Set G))))).Normal := fun k =>
    not_normal_neighbour_pairTorus_of_twoSided_four plusFourLeviInput_holds
      plusFourRefinedF6Input_holds hset hKc hq e htC ht hR5 k rfl rfl
  have hrow : ∀ k : Fin 4, OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) .field := fun k =>
    (omegaRowAt_pairTorus_iff (by norm_num) e htC 0 k .field).1 hrow0
  obtain ⟨x, z, hz, hxz, h1, h2, -⟩ := hR5
  exact plusNode_zero_le_centralizer_plusNode_two_three hset hcat
    (LinearPilot.slmEvenTypeDetAt (by norm_num)) hKc hq e ht hKt ⟨x, z, hz, hxz, h1, h2⟩ hnn hrow
    ι hσ hfix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_omegaPlus_four_of_orthCat (hres : OmegaPlusFourResidualInput)
    (hcat : SLmCatalogueClausesAt 4)
    (huniq : OmegaPlusFourUniqueInput) (hend : OmegaPlusFourEndInput)
    (hswap : OmegaPlusFourSwapInput) (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    False := by
  have horth := omegaPlusFourOrthCatInput_holds
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hR5 := exists_conj_eq_mul_longRoot_twoSided_four_of_inputs hres hset hKc hf e ht hKt
  have hnn := not_normal_neighbour_pairTorus_four_of_inputs plusFourLeviInput_holds
    plusFourRefinedF6Input_holds hres hset hKc hf e ht hKt
  obtain ⟨r, hr0⟩ := exists_omegaRowAt_pairTorus_four hset hKc hq 0 e htC ht
  have hr : ∀ k : Fin (3 + 1), OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) r := fun k =>
    (omegaRowAt_pairTorus_iff (by norm_num) e htC 0 k r).1 hr0
  cases r with
  | swap => exact hswap G L hset f K hKc hf e t ht hKt hR5 hnn hr
  | field =>
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
    have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
    have hF : Nat.card F = 2 ^ (2 * f) :=
      SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
    have hC : ∀ k, PlusFieldCover e ι k := fun k =>
      (omegaPlusFourCoverInput_of_catalogue hcat G L hset f K hKc hf e t ht hKt k (hnn k) (hr k) F
        ι σ hσ hfix).some
    have horth' := horth hcat G L hset f K hKc hf e t ht hKt hR5 hr0 F ι σ hσ hfix
    obtain ⟨-, -, -, hLG, -, -, htN, hcl⟩ :=
      fieldRow_global_four hset hKc hq e htC ht hF hC horth' (G₀ := ⨆ j, plusNode e j) rfl
    obtain ⟨ψ, hψ⟩ := hcl σ hσ
    exact hend G L hset t ht hKt _ hLG htN F σ hσ ψ hψ
      (huniq G L hset f K hKc hf e t ht hKt F ι σ hσ hfix _ rfl ⟨ψ⟩)

theorem omegaPlusFourInput_of_orthCat (hres : OmegaPlusFourResidualInput)
    (hcat : SLmCatalogueClausesAt 4)
    (huniq : OmegaPlusFourUniqueInput) (hend : OmegaPlusFourEndInput)
    (hswap : OmegaPlusFourSwapInput) : OmegaPlusFourInput := by
  intro G _ _ L hset f K _ _ _ hK hf e t ht hKt
  exact false_of_omegaPlus_four_of_orthCat hres hcat huniq hend hswap hset hK hf e ht hKt

theorem omegaPlusFourInput_of_catalogue_four (hres : OmegaPlusFourResidualInput)
    (hcat : SLmCatalogueClausesAt 4) (huniq : OmegaPlusFourUniqueInput)
    (hend : OmegaPlusFourEndInput) (hswap : OmegaPlusFourSwapInput) : OmegaPlusFourInput :=
  omegaPlusFourInput_of_orthCat hres hcat huniq hend hswap

end Main

end CFSG.SeitzReduction.OmegaPilot
