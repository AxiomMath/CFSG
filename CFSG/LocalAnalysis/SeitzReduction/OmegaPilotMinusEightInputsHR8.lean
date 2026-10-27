module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8FieldNormal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourCore
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHR8Field

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (SUmCatalogueClausesAt NeighbourOvergroupSUm
  SUmNeighbourAlternative)

section HR8

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_minusPairTorus_four (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (4 - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (n := 4) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (n := 4) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSUm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        SUmNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 4 f := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨hcomp, hsyl, hstd⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le hset
    hKc hq le_rfl hirr k e htC ht hX htX hDe
  have hnn := not_normal_neighbour_minusPairTorus_of_four_le hset hKc hq le_rfl hirr e htC ht k hX
    hDe
  obtain ⟨-, -, -, hcardX, -, -, hDC, hDq, hZ, -⟩ :=
    neighbour_data_minusPairTorus_of_four_le hKc hq le_rfl hirr k e htC hX hDe
  have hDm : LieModel (D ⧸ center D) .PSU 4 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
      (lieModel_map_minusPairPerp_four hKc hirr k e hDe)
  have hZD : Odd (Nat.card (center D)) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  have hXne : X ≠ ⊥ := by
    intro hXb
    have h1 : Nat.card X = 1 := by rw [hXb, Subgroup.card_bot]
    omega
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  have hmf : ((4 : ℕ), f) ≠ (4, 1) := by
    intro h'
    rw [Prod.mk.injEq] at h'
    omega
  exact UnitaryPilot.neighbour_overgroup_sum le_rfl hmf hcat hset.standardSetting.kProper
    (F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple hset.standardSetting.nonab
      hXne) htX ht (hDC.trans inf_le_left) hDq hDm hZD hcomp hsyl hstd hnn

end HR8

section Normal


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem graphField_neighbour_minusPairTorus_four (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (4 - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (n := 4) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (n := 4) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    (hKcomp : IsComponent Kc)
    (hDK : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom = Kc) :
    ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
        normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))),
      ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ (2 * f) ∧
        ∃ (eK : Kc ≃* LinearFlag.projectiveSL 4 K') (φ : K' ≃+* K'),
          (∀ x, φ x = x ^ 2 ^ f) ∧
          MulAut.congr eK (Kc.normalizerMonoidHom ⟨_, hsN⟩) =
            LinearFlag.fieldAut 4 K' φ * LinearFlag.dualAut 4 K' := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le hset
    hKc hq le_rfl hirr k e htC ht hX htX hDe
  obtain ⟨-, -, -, -, -, -, hDC, hDq, hZ, -⟩ :=
    neighbour_data_minusPairTorus_of_four_le hKc hq le_rfl hirr k e htC hX hDe
  have hDm : LieModel (D ⧸ center D) .PSU 4 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
      (lieModel_map_minusPairPerp_four hKc hirr k e hDe)
  have hDm' := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple
    (hDC.trans inf_le_left) hDq hDm (ne_bot_of_isQuasisimple hcomp.2.2)
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  have hmf : ((4 : ℕ), f) ≠ (4, 1) := by
    intro h'
    rw [Prod.mk.injEq] at h'
    omega
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact ((neighbour_overgroup_minusPairTorus_four hset hcat hKc hq hirr k e htC ht hX htX
    hDe).2 Kc hKcomp hDK).graphField (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _)
    (orderOf_mk_oddCore ht') hcomp le_rfl hmf (UnitaryPilot.sumEvenTypeDetAt le_rfl) hDm' hKcomp
    hKt

theorem neighbourCore_minusPairTorus_four (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (4 - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (n := 4) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (n := 4) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    (hKcomp : IsComponent Kc)
    (hDK : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom = Kc) :
    ∃ hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
        normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))),
      Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
      center Kc = ⊥ ∧
      (∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ (2 * f) ∧
        ∃ (eK : Kc ≃* LinearFlag.projectiveSL 4 K') (φ : K' ≃+* K'),
          (∀ x, φ x = x ^ 2 ^ f) ∧
          MulAut.congr eK (Kc.normalizerMonoidHom ⟨_, hsN⟩) =
            LinearFlag.fieldAut 4 K' φ * LinearFlag.dualAut 4 K') ∧
      ∃ q : F4Pilot.centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker = center (F4Pilot.centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        (∀ y : F4Pilot.centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) =
            QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
              ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩) ∧
        (∃ htE : t ∈ normalizer (F4Pilot.centralizerPerfectCore X : Set G),
          ∀ y : F4Pilot.centralizerPerfectCore X,
            q ((F4Pilot.centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ y) =
              Kc.normalizerMonoidHom ⟨_, hsN⟩ (q y)) ∧
        ∃ hDE : D ≤ F4Pilot.centralizerPerfectCore X,
          Function.Injective (q.comp (Subgroup.inclusion hDE)) ∧
            (q.comp (Subgroup.inclusion hDE)).range =
              ((D.subgroupOf (centralizer (X : Set G))).map
                (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le hset
    hKc hq le_rfl hirr k e htC ht hX htX hDe
  obtain ⟨-, -, -, -, -, -, hDC, hDq, hZ, -⟩ :=
    neighbour_data_minusPairTorus_of_four_le hKc hq le_rfl hirr k e htC hX hDe
  have hDm : LieModel (D ⧸ center D) .PSU 4 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
      (lieModel_map_minusPairPerp_four hKc hirr k e hDe)
  have hDm' := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple
    (hDC.trans inf_le_left) hDq hDm (ne_bot_of_isQuasisimple hcomp.2.2)
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  have hmf : ((4 : ℕ), f) ≠ (4, 1) := by
    intro h'
    rw [Prod.mk.injEq] at h'
    omega
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have halt := (neighbour_overgroup_minusPairTorus_four hset hcat hKc hq hirr k e htC ht hX htX
    hDe).2 Kc hKcomp hDK
  obtain ⟨⟨-, ⟨-, hDK', -, hsN, hout, hZK, -, -⟩ | ⟨hKt', -⟩⟩, -⟩ :=
    halt.field (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) (orderOf_mk_oddCore ht') hcomp
      le_rfl hmf (UnitaryPilot.sumEvenTypeDetAt le_rfl) hDm' hKcomp
  · obtain ⟨hsN', K', _, _, hK', eK, φ, hφ, hτ⟩ := graphField_neighbour_minusPairTorus_four hset
      hcat hKc hq hirr k e htC ht hX htX hDe Kc hKcomp hDK hKt
    have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer Kc) :=
      LinearPilot.isSolvable_outer_of_mulEquiv (by norm_num) eK
    obtain ⟨hLt, hD, -, hXo⟩ :=
      bLift_inputs_minusPairTorus_of_four_le hset hKc hq le_rfl hirr k e htC ht hX hDe
    obtain ⟨-, -, q, hqs, hqker, hkodd, hqapp⟩ := exists_surjective_neighbourCore_of_field htC ht
      hLt htX hD hDq hXo hsyl hKcomp hDK'.le hsN hout hOut
    refine ⟨hsN, hout, hZK, ⟨K', inferInstance, inferInstance, hK', eK, φ, hφ, hτ⟩, q, hqs,
      LinearPilot.ker_eq_center_of_surjective_of_center_eq_bot hqs hqker hZK, hkodd, hqapp,
      exists_mem_normalizer_neighbourCore_comm htX hsN q hqapp, ?_⟩
    exact exists_injective_neighbourCore_restrict (hDC.trans inf_le_left) hDq hZ q hqker hqapp
  · exact absurd hKt hKt'

end Normal

end CFSG.SeitzReduction.OmegaPilot
