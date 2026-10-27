module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeCoverPlus

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  coordinateFieldMap matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl fieldAutT fieldAutT_mk
  matrixDerivedConjugation_fieldPair_val)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Frob

variable {F : Type} [Field F] [CharP F 2] {m : ℕ}

theorem statedOmegaPlusEquiv_congr (hm : 1 ≤ m) (σ : F ≃+* F)
    (hQσ : ∀ v, coordinateQuadPlus m F (coordinateFieldMap _ σ v) = σ (coordinateQuadPlus m F v))
    (A : StatedOmega (StatedQuadPlus m F)) :
    statedOmegaPlusEquiv F m hm (statedOmegaPlusCongr σ m A) =
      fieldAutT (coordinateQuadPlus m F) σ hQσ (statedOmegaPlusEquiv F m hm A) := by
  change matrixProjectiveProjection _ (statedDerivedPlusEquiv F m (statedOmegaPlusCongr σ m A)) =
    fieldAutT _ σ hQσ (matrixProjectiveProjection _ (statedDerivedPlusEquiv F m A))
  rw [fieldAutT_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_fieldPair_val]
  apply Units.ext
  ext i j
  have h1 := CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedDerivedReindexEquiv_entry (plusIndexEquiv m)
    (CFSG.LieType.Universal.Spin.quadPlus m F) (CFSG.LieType.Universal.Spin.coe_quadPlus m F)
    (statedOmegaPlusCongr σ m A) i j
  have h2 := CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedDerivedReindexEquiv_entry (plusIndexEquiv m)
    (CFSG.LieType.Universal.Spin.quadPlus m F) (CFSG.LieType.Universal.Spin.coe_quadPlus m F)
    A i j
  change (statedDerivedPlusEquiv F m (statedOmegaPlusCongr σ m A)).val.val i j =
    σ ((statedDerivedPlusEquiv F m A).val.val i j)
  refine h1.trans ?_
  rw [show (statedDerivedPlusEquiv F m A).val.val i j = _ from h2]
  rfl

theorem statedOmegaPlusEquiv_symm_fieldAutT (hm : 1 ≤ m) (σ : F ≃+* F)
    (hQσ : ∀ v, coordinateQuadPlus m F (coordinateFieldMap _ σ v) = σ (coordinateQuadPlus m F v))
    (y : matrixProjectiveDerived (coordinateQuadPlus m F)) :
    (statedOmegaPlusEquiv F m hm).symm (fieldAutT (coordinateQuadPlus m F) σ hQσ y) =
      statedOmegaPlusCongr σ m ((statedOmegaPlusEquiv F m hm).symm y) := by
  rw [MulEquiv.symm_apply_eq, statedOmegaPlusEquiv_congr hm σ hQσ, MulEquiv.apply_symm_apply]

end Frob

section Cover

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_plusFieldCover_conj_four (hset : SeitzSetting G L) (hcat : SLmCatalogueClausesAt 4)
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
    ∃ C : PlusFieldCover (m := 3) e ι k, ∀ x : plusNeighbourCore e k,
      C.π ((plusNeighbourCore e k).normalizerMonoidHom ⟨t,
        UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _⟩ x) =
      statedOmegaPlusCongr σ 3 (C.π x) := by
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
    obtain ⟨ψ, hψ, hψτ⟩ := plusNormalizationThree_of_isComponent F σ hσ ι.fieldRange hσk f hk₀ Kc
      (Kc.normalizerMonoidHom ⟨_, hsN⟩) hτ2 hmodel hall hout _ (q.comp (Subgroup.inclusion hDE))
      hqinj hεfix hεcomp (pairPerpFieldEquiv e (by norm_num) k ι.rangeRestrictFieldEquiv)
    refine ⟨PlusFieldCover.ofNormalized
      ((statedOmegaPlusEquiv F 3 (by omega)).symm.toMonoidHom.comp (ψ.toMonoidHom.comp q))
      ((statedOmegaPlusEquiv F 3 (by omega)).symm.surjective.comp (ψ.surjective.comp hqs))
      (fun x hx => ?_) hDE (fun t' ht' hmem => ?_), fun x => ?_⟩
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
      have hτ := congrArg (fun α : MulAut _ => α (ψ (q x))) hψτ
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hτ
      change (statedOmegaPlusEquiv F 3 (by omega)).symm
          (ψ (q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ x))) =
        statedOmegaPlusCongr σ 3 ((statedOmegaPlusEquiv F 3 (by omega)).symm (ψ (q x)))
      rw [hqt x]
      exact (congrArg (statedOmegaPlusEquiv F 3 (by omega)).symm hτ).trans
        (statedOmegaPlusEquiv_symm_fieldAutT _ σ _ _)
  · exfalso
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

end Cover

end CFSG.SeitzReduction.OmegaPilot
