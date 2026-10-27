module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBSpor
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2Ten
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

theorem omega_not_inner_four_one (h : OmegaCatalogueClausesAt 4)
    (hspor : OmegaEightSporadicStatement) {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (hcat : Catalog (K ⧸ center K)) (τ : MulAut K) (hτ : orderOf τ = 2) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (D : Subgroup (fixedSubgroup τ))
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) t 4 2 1)
    (hZD : Odd (Nat.card (center D))) (hsmall : FixedCentralizerTwoSmall τ D) :
    τ ∉ (MulAut.conj : K →* MulAut K).range := by
  intro hin
  have hsm := omega_inner_small_of_clauses h hK hcat τ hτ ht D hD hDm hZD hin hsmall
  obtain ⟨hτ', hinn, D', hD', hD'm, -⟩ := h.2.2.2.2.2 K hK τ hτ t 4 1 D hD hDm
  exact (hspor (K ⧸ center K) hK.2.1 hK.2.2 hsm.2.2 _ hτ' t D' ht hD' hD'm).1 (hinn hin)

theorem neighbour_overgroup_omega_four_one_of_pPrimeCore_eq_bot
    (hcat : OmegaCatalogueClausesAt 4) (hspor : OmegaEightSporadicStatement) {Y : Type}
    [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    {tag : StatedLieTag} (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus)
    (hDm : LieModel (D ⧸ center D) tag 4 2 1) (hZD : Odd (Nat.card (center D))) :
    NeighbourOvergroupOmega s D 4 1 ∧
      ∀ Lc : Subgroup Y, IsComponent Lc → ⁅D, Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative s D Lc 4 1 := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, hiff, hfix, hswap⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  have hK : OmegaNeighbourAlternative s D Kc 4 1 := by
    refine ⟨hDKK, ?_⟩
    by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
    · left
      obtain ⟨hDK, hDcomp⟩ := hfix hKt
      have hDne : D ≠ Kc := by
        rintro rfl
        exact hnn (F4Pilot.normal_of_isComponent_of_standard hKc hstd)
      have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
      have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := by
        intro hKs
        rw [inf_eq_left.mpr hKs] at hDcomp
        exact hDne (F4Pilot.eq_of_isComponent_subgroupOf hKc.1 hDK hDcomp)
      have hτ2 := F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
      obtain ⟨hD'c, hD'm, hD'map, hD'Z⟩ :=
        UnitaryPilot.isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK hDs hDcomp hDm
      have hcatK := hsec Kc hKc
      have hsK : s ∉ Kc := fun hsK =>
        omega_not_inner_four_one hcat hspor hKc.1 hcatK _ hτ2 htag _ hD'c hD'm (hD'Z ▸ hZD)
          (E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK hsyl _ hD'map)
          (F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK)
      exact ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN, omega_overgroup_catalogue hcat
        hKc.1 hcatK _ hτ2 htag _ hD'c hD'm
        (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl _ hD'map)⟩
    · right
      obtain ⟨hcomm, -, hdiag, -⟩ := hswap hKt
      exact ⟨hKt, hcomm,
        LinearPilot.center_eq_bot_and_nonempty_mulEquiv_of_swap hO hs hKc hKt hcomm hdiag hDs
          hsyl⟩
  refine ⟨⟨Kc, hKc, hK⟩, fun Lc hLc hDLc => ?_⟩
  rcases (hiff Lc hLc).1 hDLc with rfl | rfl
  · exact hK
  · by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
    · rw [hKt]
      exact hK
    · obtain ⟨-, ⟨hKt', -⟩ | ⟨-, hcomm, hZ, hφ⟩⟩ := hK
      · exact absurd hKt' hKt
      · exact OmegaNeighbourAlternative.map_conj_of_swap hs2 hDKK hKt hcomm hZ hφ

theorem neighbour_overgroup_omega_four_one (hcat : OmegaCatalogueClausesAt 4)
    (hspor : OmegaEightSporadicStatement) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G))
    (hDq : CFSG.IsQuasisimple D) {tag : StatedLieTag}
    (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus) (hDm : LieModel (D ⧸ center D) tag 4 2 1)
    (hZD : Odd (Nat.card (center D)))
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 1 := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => F4Pilot.catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hne := ne_bot_of_isQuasisimple hcomp.2.2
  exact (neighbour_overgroup_omega_four_one_of_pPrimeCore_eq_bot hcat hspor
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn htag
    (UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq hDm hne)
    (UnitaryPilot.odd_card_center_map_subgroupOf_oddCore hDX hDq hZD hne)).1

theorem neighbour_overgroup_omega_four_one_of_seitzSetting {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : SeitzSetting G L) (hcat : OmegaCatalogueClausesAt 4)
    (hspor : OmegaEightSporadicStatement) {X : Subgroup G} (hX : X ≠ ⊥)
    {t : G} (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2) {D : Subgroup G}
    (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.IsQuasisimple D) (hZD : center D = ⊥)
    {tag : StatedLieTag} (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus)
    (hDm : LieModel D tag 4 2 1)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 1 :=
  neighbour_overgroup_omega_four_one hcat hspor hset.standardSetting.kProper
    (F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple hset.standardSetting.nonab
      hX) htX ht hDX hDq htag (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZD hDm)
    (odd_card_center_of_center_eq_bot hZD) hcomp hsyl hstd hnn

section Instances

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_anisoTorus_five_two (hset : SeitzSetting G L)
    (hcat : OmegaCatalogueClausesAt 4) (hspor : OmegaEightSporadicStatement) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by norm_num) b c).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by norm_num) b c).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 1 := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, -, -, -, -, hDC, hDq, hZ⟩ := neighbour_data_anisoTorus (by norm_num) hirr e htC hX hDe
  obtain ⟨hLie, -⟩ := lieModel_map_anisoPerp hKc le_rfl hirr e hDe
  have hreg := regular_coordinateQuadMinus 5 K b c (by norm_num) hirr
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e.symm.injective]
    exact (isAnisoCoord_coordinateQuadMinus (by norm_num) hirr).anisoTorusOf_ne_bot hreg.1 hreg.2
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_anisoTorus_of_seitzSetting hset hKc (by norm_num) hirr e htC ht hX htX hDe
  exact neighbour_overgroup_omega_four_one_of_seitzSetting hset hcat hspor hXne htX ht
    (hDC.trans inf_le_left) hDq hZ (Or.inl rfl) hLie hcomp hsyl hstd hnn

theorem neighbour_overgroup_plusAnisoTorus_three_two (hset : SeitzSetting G L)
    (hcat : OmegaCatalogueClausesAt 4) (hspor : OmegaEightSporadicStatement) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((plusAnisoTorus 3 hirr).map
      (e.trans (plusAnisoProjEquiv 3 hirr).symm).symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((plusAnisoPerp (K := K) 3 b c).map
      (e.trans (plusAnisoProjEquiv 3 hirr).symm).symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 1 := by
  set e' := e.trans (plusAnisoProjEquiv 3 hirr).symm with he'
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  have hKt := inf_centralizer_eq_zpowers_plus hset (by norm_num) hKc e htC ht
  obtain ⟨-, -, -, -, -, hDC, hDq, hZ⟩ := neighbour_data_plusAnisoTorus le_rfl hirr e' htC hX hDe
  obtain ⟨hLie, -⟩ := lieModel_map_plusAnisoPerp hKc le_rfl hirr e' hDe
  have hreg := regular_plusAnisoQuad (K := K) (b := b) (c := c)
    (coeff_ne_zero_of_irreducible' hirr) (by norm_num : 1 ≤ 3)
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e'.symm.injective]
    exact (isAnisoCoord_plusAnisoQuad hirr).anisoTorusOf_ne_bot hreg.1 hreg.2
  obtain ⟨hcomp, hsyl, hstd⟩ := neighbour_standard_plusAnisoTorus hset.standardSetting.standard
    htC ht hKt le_rfl hirr e' hX htX hDe
  exact neighbour_overgroup_omega_four_one_of_seitzSetting hset hcat hspor hXne htX ht
    (hDC.trans inf_le_left) hDq hZ (Or.inr rfl) hLie hcomp hsyl hstd hnn

end Instances

theorem omegaMinusTwoTenHR8Input_of_clauses (hcat : OmegaCatalogueClausesAt 4)
    (hspor : OmegaEightSporadicStatement) : OmegaMinusTwoTenHR8Input := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX
  exact neighbour_overgroup_anisoTorus_five_two hset hcat hspor hK2 hirr e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht rfl htX rfl hnn

theorem omegaPlusTwoTenHR8Input_of_clauses (hcat : OmegaCatalogueClausesAt 4)
    (hspor : OmegaEightSporadicStatement) : OmegaPlusTwoTenHR8Input := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX
  exact neighbour_overgroup_plusAnisoTorus_three_two hset hcat hspor hK2 hirr e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht rfl htX rfl hnn

end CFSG.SeitzReduction.OmegaPilot
