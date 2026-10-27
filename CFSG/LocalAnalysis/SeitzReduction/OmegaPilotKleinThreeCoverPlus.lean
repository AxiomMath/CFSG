module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourMain
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreePlus

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt NeighbourOvergroupSLm
  NeighbourOvergroupSLmField)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section HR8

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem lieModel_quotient_center_pairPerp_four {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {D : Subgroup G}
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    LieModel (D ⧸ center D) .PSL 4 2 f := by
  subst hDe
  obtain ⟨φ⟩ := nonempty_pairPerp_mulEquiv_SL4 hq k
  exact LinearPilot.lieModel_of_mulEquiv_projectiveSL (by norm_num)
    (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
    (LinearPilot.quotientCenterEquivProjectiveSL
      ((LinearPilot.mapSymmMulEquiv e (pairPerp (K := K) k)).trans φ))

theorem neighbour_overgroup_pairTorus_four (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 f := by
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting_four hset hKc hq k e htC ht hX htX hDe
  obtain ⟨-, -, -, hXc, -, -, hDC, hDq, -⟩ := neighbour_data_pairTorus_four hKc hq k e htC hX hDe
  have hDm := lieModel_quotient_center_pairPerp_four hKc hq k e hDe
  have hXne : X ≠ ⊥ := by
    intro hXb
    rw [hXb, Subgroup.card_bot] at hXc
    omega
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  exact LinearPilot.neighbour_overgroup_slm_center (by norm_num) (Or.inr hf2) hcat
    hset.standardSetting.kProper
    (F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple hset.standardSetting.nonab
      hXne) htX ht (hDC.trans inf_le_left) hDq hDm hcomp hsyl hstd hnn

theorem neighbour_overgroup_pairTorus_four_field (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) {f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 f ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ := by
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting_four hset hKc hq k e htC ht hX htX hDe
  obtain ⟨-, -, -, -, -, -, hDC, hDq, -⟩ := neighbour_data_pairTorus_four hKc hq k e htC hX hDe
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  exact LinearPilot.NeighbourOvergroupSLm.field_oddCore htX ht (hDC.trans inf_le_left) hDq
    (by norm_num) (Or.inr hf2) hdet (lieModel_quotient_center_pairPerp_four hKc hq k e hDe) hcomp
    (neighbour_overgroup_pairTorus_four hset hcat hKc hq k e htC ht hX htX hDe hnn)

theorem neighbourCore_pairTorus_four (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    (hKcomp : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hZK : center Kc = ⊥) (hmodel : LieModel Kc .PSL 4 2 (2 * f)) :
    ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
      q.ker = center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
      (∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
        oddCore (centralizer (X : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩) ∧
      (∃ htE : t ∈ normalizer (centralizerPerfectCore X : Set G),
        ∀ y : centralizerPerfectCore X,
          q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ y) =
            Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y)) ∧
      ∃ hDE : D ≤ centralizerPerfectCore X,
        Function.Injective (q.comp (Subgroup.inclusion hDE)) ∧
          (q.comp (Subgroup.inclusion hDE)).range =
            ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc := by
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting_four hset hKc hq k e htC ht hX htX hDe
  obtain ⟨-, -, -, -, -, hD, hDC, hDq, hZD, -⟩ :=
    neighbour_data_pairTorus_four hKc hq k e htC hX hDe
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hK := inf_centralizer_eq_zpowers_plus hset (by norm_num) hKc e htC ht
  have hXo := mem_of_odd_of_commute_pairTorus_four htC ht hLt hK (by omega) k e hX hDe
  obtain ⟨F, _, _, -, ⟨ε⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel
      (CFSG.ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hmodel).1 hmodel
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer Kc) :=
    LinearPilot.isSolvable_outer_of_mulEquiv (by norm_num)
      (ε.trans (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 4 F).symm))
  obtain ⟨-, -, q, hqs, hqker, hkodd, hqapp⟩ := exists_surjective_neighbourCore_of_field htC ht
    hLt htX hD hDq hXo hsyl hKcomp hDK hsN hout hOut
  exact ⟨q, hqs, LinearPilot.ker_eq_center_of_surjective_of_center_eq_bot hqs hqker hZK, hkodd,
    hqapp, exists_mem_normalizer_neighbourCore_comm htX hsN q hqapp,
    exists_injective_neighbourCore_restrict (hDC.trans inf_le_left) hDq hZD q hqker hqapp⟩

end HR8

section Cover

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_plusFieldCover_four (hset : SeitzSetting G L) (hcat : SLmCatalogueClausesAt 4)
    (hdet : LinearPilot.SLmEvenTypeDetAt 4) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hnn : ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
          (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
            Set G))))).Normal)
    (hrow : OmegaRowAt t (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k))
      .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (PlusFieldCover (m := 3) e ι k) := by
  set X := modelToG e (pairTorus (K := K) k) with hXdef
  set D := modelToG e (pairPerp (K := K) k) with hDdef
  obtain ⟨htX, -⟩ := id hrow
  obtain ⟨-, -, -, -, -, -, hDC, -⟩ := neighbour_data_pairTorus_four (X := X) (D := D) hKc hq k e
    htC rfl rfl
  obtain ⟨⟨Kc, hKcomp, hDKK, hcase⟩, -⟩ := neighbour_overgroup_pairTorus_four_field (X := X)
    (D := D) hset hcat hdet hKc hq k e htC ht rfl htX rfl hnn
  rcases hcase with ⟨-, hDK, -, hsN, hout, hZK, hmodel, hall⟩ | ⟨hKt', -, -, -⟩
  · obtain ⟨q, hqs, hqker, -, -, ⟨htE, hqt⟩, hDE, hqinj, hqrange⟩ :=
      neighbourCore_pairTorus_four (X := X) (D := D) hset hKc hq k e htC ht rfl htX rfl Kc hKcomp
        hDK.le hsN hout hZK hmodel
    have hcompD := (neighbour_standard_pairTorus_of_seitzSetting_four (X := X) (D := D) hset hKc
      hq k e htC ht rfl htX rfl).1
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
      hqinj hεfix hεcomp (pairPerpFieldEquiv e (by norm_num) k ι.rangeRestrictFieldEquiv)
    refine ⟨PlusFieldCover.ofNormalized
      ((statedOmegaPlusEquiv F 3 (by omega)).symm.toMonoidHom.comp (ψ.toMonoidHom.comp q))
      ((statedOmegaPlusEquiv F 3 (by omega)).symm.surjective.comp (ψ.surjective.comp hqs))
      (fun x hx => ?_) hDE (fun t' ht' hmem => ?_)⟩
    · have hx' : ψ (q x) = 1 := by
        have h1 := MonoidHom.mem_ker.1 hx
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
        exact (MulEquiv.map_eq_one_iff _).1 h1
      have h2 : x ∈ q.ker := MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ψ).1 hx')
      rw [hqker] at h2
      exact h2
    · have hgD := symm_mem_modelToG e (frameHom_mem_pairPerp (K := K) ht')
      have hw' : liftParam ι.fieldRange.subtype
          (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t')) =
          liftParam ι (restrictParam k t') := by
        funext l
        apply Units.ext
        simp [liftParam]
      have hjF : pairPerpFieldEquiv e (by norm_num) k ι.rangeRestrictFieldEquiv ⟨_, hgD⟩ =
          (isHypFrame_plus ι.fieldRange 3).frameHom
            (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t')) :=
        pairPerpFieldEquiv_frameHom e (by norm_num) k _ ht' hgD
      change (((statedOmegaPlusEquiv F 3 (by omega)).symm
        (ψ ((q.comp (Subgroup.inclusion hDE)) ⟨_, hgD⟩)) :
          StatedOmega (StatedQuadPlus 3 F)) : GL (Fin 3 ⊕ Fin 3) F) = _
      rw [hψ]
      erw [hjF]
      rw [incl_frameHom, statedOmegaPlusEquiv_symm_frameHom, hw', neighbourDiag_apply]
  ·
    exfalso
    have hswap : OmegaRowAt t X D .swap :=
      ⟨htX, Kc, hKcomp, hDKK, iff_of_false (by decide) hKt'⟩
    have hDq : ∀ htX' : t ∈ centralizer (X : Set G), CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX'⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) := fun htX' =>
      (neighbour_standard_pairTorus_of_seitzSetting_four (X := X) (D := D) hset hKc hq k e htC ht
        rfl htX' rfl).1
    exact absurd (OmegaRowAt.unique ht hDq hrow hswap) (by decide)

theorem omegaPlusFourCoverInput_of_catalogue_typeDet (hcat : SLmCatalogueClausesAt 4)
    (hdet : LinearPilot.SLmEvenTypeDetAt 4) : OmegaPlusFourCoverInput := by
  intro G _ _ L hset f K _ _ _ hKc hf2 e t ht hKt k hnn hrow F _ _ _ ι σ hσ hfix
  exact nonempty_plusFieldCover_four hset hcat hdet hKc
    ((LinearPilot.four_le_card_iff_two_le hKc).2 hf2) k e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht hnn hrow ι hσ hfix

section Certificates

theorem omegaPlusFourCoverInput_of_catalogue (hcat : SLmCatalogueClausesAt 4) :
    OmegaPlusFourCoverInput :=
  omegaPlusFourCoverInput_of_catalogue_typeDet hcat (LinearPilot.slmEvenTypeDetAt (by norm_num))

end Certificates

end Cover

end CFSG.SeitzReduction.OmegaPilot
