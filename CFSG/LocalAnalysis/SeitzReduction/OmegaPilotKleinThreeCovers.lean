module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreePlus
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputs
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsAnisoCover

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)

section Split


theorem omegaMinusFourCoverInput_of_catalogue (hcat : UnitaryPilot.SUmCatalogueClausesAt 4) :
    OmegaMinusFourCoverInput :=
  omegaMinusFourCoverInput_of_normalization minusNormalizationThreeInput_holds hcat

end Split

section Aniso

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_minusAnisoFieldCover_four (hset : SeitzSetting G L)
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) {f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hrow : OmegaRowAt t (modelToG e (anisoTorus (K := K) (n := 2 + 2) (by omega) b c))
      (modelToG e (anisoPerp (K := K) (n := 2 + 2) (by omega) b c)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (MinusAnisoFieldCover (r := 2) e ι) := by
  set X := modelToG e (anisoTorus (K := K) (n := 2 + 2) (by omega) b c) with hXdef
  set D := modelToG e (anisoPerp (K := K) (n := 2 + 2) (by omega) b c) with hDdef
  obtain ⟨htX, -⟩ := id hrow
  obtain ⟨-, -, -, -, -, hDC, -, -⟩ :=
    neighbour_data_anisoTorus (X := X) (D := D) le_rfl hirr e htC rfl rfl
  obtain ⟨⟨Kc, hKcomp, hDKK, hcase⟩, -⟩ := neighbour_overgroup_anisoTorus_four_field (X := X)
    (D := D) hset hcat hdet hKc hq hirr e htC ht rfl htX rfl
  rcases hcase with ⟨-, hDK, -, hsN, hout, hZK, hmodel, hall⟩ | ⟨hKt', -, -, -⟩
  · obtain ⟨q, hqs, hqker, -, -, ⟨htE, hqt⟩, hDE, hqinj, hqrange⟩ := neighbourCore_anisoTorus_four
      (X := X) (D := D) hset hKc hirr e htC ht rfl htX rfl Kc hKcomp hDK.le hsN hout hZK hmodel
    have hcompD := (neighbour_standard_anisoTorus_of_seitzSetting (X := X) (D := D) hset hKc
      le_rfl hirr e htC ht rfl htX rfl).1
    have hDs := hcompD.1
    have hDc := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcompD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    have hD'c := F4Pilot.isComponent_subgroupOf_subgroupOf
      (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
    have hεcomp : CFSG.IsComponent ((q.comp (Subgroup.inclusion hDE)).range.subgroupOf
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))) := by
      rw [hqrange]
      exact hD'c
    have ht2 : t ^ 2 = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    have hs2 : (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have h1 : (⟨t, htX⟩ : centralizer (X : Set G)) ^ 2 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact ht2)
      rw [h1, map_one]
    have hτ2 : Kc.normalizerMonoidHom ⟨_, hsN⟩ * Kc.normalizerMonoidHom ⟨_, hsN⟩ = 1 := by
      rw [← _root_.sq]
      exact F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hs2
    have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
      rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
    have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
    have hk₀ : Nat.card ι.fieldRange = 2 ^ f :=
      (Nat.card_congr ι.rangeRestrictFieldEquiv.toEquiv).symm.trans hKc
    have hεfix : (q.comp (Subgroup.inclusion hDE)).range ≤
        fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩) := by
      rintro _ ⟨d, rfl⟩
      change Kc.normalizerMonoidHom ⟨_, hsN⟩ (q (Subgroup.inclusion hDE d)) =
        q (Subgroup.inclusion hDE d)
      rw [← hqt]
      congr 1
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * (d : G) * t⁻¹ = d
      rw [mem_centralizer_iff.1 (hDC d.2).2 t (Set.mem_singleton t), mul_inv_cancel_right]
    obtain ⟨ψ, hψ, -⟩ := plusNormalizationThree_of_isComponent F σ hσ ι.fieldRange hσk f hk₀ Kc
      (Kc.normalizerMonoidHom ⟨_, hsN⟩) hτ2 hmodel hall hout _ (q.comp (Subgroup.inclusion hDE))
      hqinj hεfix hεcomp (anisoPerpFieldEquiv hirr e ι.rangeRestrictFieldEquiv)
    let π0 := (statedOmegaPlusEquiv F (2 + 1) (by omega)).symm.toMonoidHom.comp
      (ψ.toMonoidHom.comp q)
    have hs0 : Function.Surjective π0 :=
      (statedOmegaPlusEquiv F (2 + 1) (by omega)).symm.surjective.comp (ψ.surjective.comp hqs)
    have hk0 : π0.ker ≤ center (anisoNeighbourCore e) := by
      intro x hx
      have hx' : ψ (q x) = 1 := by
        have h1 := MonoidHom.mem_ker.1 hx
        simp only [π0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
        exact (MulEquiv.map_eq_one_iff _).1 h1
      have h2 : x ∈ q.ker := MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ψ).1 hx')
      rw [hqker] at h2
      exact h2
    have hT : ∀ t' : Fin (2 + 1) → Kˣ,
        ((e.symm ((isHypFrame_minus K (n := 2 + 2) (by omega) b c).frameHom t') : L) : G) ∈
          anisoNeighbourCore e := fun t' =>
      hDE (symm_mem_modelToG e (frameHom_mem_anisoPerp (n := 2 + 2) (by omega) t'))
    have hn0 : ∀ (t' : Fin (2 + 1) → Kˣ)
        (hmem : ((e.symm ((isHypFrame_minus K (n := 2 + 2) (by omega) b c).frameHom t') : L) :
          G) ∈ anisoNeighbourCore e),
        ((π0 ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus (2 + 1) F)) :
          GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) = diagOmega F (2 + 1) (liftParam ι t') := by
      intro t' hmem
      have hgD := symm_mem_modelToG e (frameHom_mem_anisoPerp (n := 2 + 2) (by omega) t')
      have hjf := anisoPerpFieldEquiv_frameHom hirr e ι.rangeRestrictFieldEquiv t' hgD
      have hinc := incl_frameHom ι.fieldRange (m := 2 + 1)
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom t')
      have hbr := statedOmegaPlusEquiv_symm_frameHom (F := F) (by omega : 1 ≤ 2 + 1)
        (liftParam ι.fieldRange.subtype (liftParam ι.rangeRestrictFieldEquiv.toRingHom t'))
      have hw : liftParam ι.fieldRange.subtype
          (liftParam ι.rangeRestrictFieldEquiv.toRingHom t') = liftParam ι t' := by
        funext l
        apply Units.ext
        simp [liftParam]
      change (((statedOmegaPlusEquiv F (2 + 1) (by omega)).symm
        (ψ ((q.comp (Subgroup.inclusion hDE)) ⟨_, hgD⟩)) :
          StatedOmega (StatedQuadPlus (2 + 1) F)) : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) = _
      rw [hψ]
      erw [hjf]
      rw [hinc, hbr, hw]
    exact ⟨MinusAnisoFieldCover.ofNormalized π0 hs0 hk0 hT hn0⟩
  ·
    exfalso
    have hswap : OmegaRowAt t X D .swap :=
      ⟨htX, Kc, hKcomp, hDKK, iff_of_false (by decide) hKt'⟩
    have hDq : ∀ htX' : t ∈ centralizer (X : Set G), CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX'⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) := fun htX' =>
      (neighbour_standard_anisoTorus_of_seitzSetting (X := X) (D := D) hset hKc le_rfl hirr e
        htC ht rfl htX' rfl).1
    exact absurd (OmegaRowAt.unique ht hDq hrow hswap) (by decide)

theorem omegaMinusFourAnisoCoverInput_of_catalogue (hrowA : OmegaMinusFourAnisoRowInput)
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    OmegaMinusFourAnisoCoverInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow F _ _ _ ι σ hσ hfix
  exact nonempty_minusAnisoFieldCover_four hset hcat hdet hKc
    ((LinearPilot.four_le_card_iff_two_le hKc).2 hf2) hirr e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht
    (hrowA G L hset f K b c hirr hKc hf2 e t ht hKt hrow) ι hσ hfix

end Aniso

section Main


theorem omegaMinusFourInput_of_catalogue (hswap : OmegaMinusFourSwapRowInput)
    (hparam : OmegaMinusFourRootParamInput) (huniq : OmegaMinusFourUniqueInput)
    (hend : OmegaMinusFourEndInput) (hcatU : UnitaryPilot.SUmCatalogueClausesAt 4)
    (hcatL : LinearPilot.SLmCatalogueClausesAt 4) (hrowA : OmegaMinusFourAnisoRowInput) :
    OmegaMinusFourInput :=
  omegaMinusFourInput_of_inputs_six hswap (omegaMinusFourCoverInput_of_catalogue hcatU)
    (omegaMinusFourAnisoCoverInput_of_catalogue hrowA hcatL
      (LinearPilot.slmEvenTypeDetAt (by norm_num)))
    hparam huniq hend

end Main

end CFSG.SeitzReduction.OmegaPilot
