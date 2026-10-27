module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourCore

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt NeighbourOvergroupSLm
  NeighbourOvergroupSLmField)

section Model

theorem nonempty_anisoPerp_four_mulEquiv_sl {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (anisoPerp (K := K) (n := 4) (by omega) b c ≃*
      Matrix.SpecialLinearGroup (Fin 4) K) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (4 - 1) K (by omega)
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (coordinateQuadPlus (4 - 1) K) hQ (by rw [Module.finrank_fin_fun]) hT hq
  set O := TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus (4 - 1) K) with hO
  have h1 : (commutator ↥O).map O.subtype = orthDerived (coordinateQuadPlus (4 - 1) K) := by
    rw [Subgroup.map_subtype_commutator]
  let e₁ : orthDerived (coordinateQuadPlus (4 - 1) K) ≃* commutator ↥O :=
    ((Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)).symm
  exact ⟨(((anisoPerpEquiv le_rfl hirr).trans e₁).trans κ).trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm⟩

theorem lieModel_quotient_center_map_anisoPerp_four {G : Type} [Group G] {L : Subgroup G} {f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (n := 4) (by omega) b c).map
      e.symm.toMonoidHom).map L.subtype) :
    LieModel (D ⧸ center D) .PSL 4 2 f := by
  subst hDe
  obtain ⟨φ⟩ := nonempty_anisoPerp_four_mulEquiv_sl hq hirr
  exact LinearPilot.lieModel_of_mulEquiv_projectiveSL (by norm_num)
    (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
    (LinearPilot.quotientCenterEquivProjectiveSL
      ((LinearPilot.mapSymmMulEquiv e (anisoPerp (K := K) (n := 4) _ b c)).trans φ))

end Model

section HR8

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_anisoTorus_four (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (n := 4) (by omega) b c).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (n := 4) (by omega) b c).map
      e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 f := by
  obtain ⟨hcomp, hsyl, hstd⟩ := neighbour_standard_anisoTorus_of_seitzSetting hset hKc le_rfl
    hirr e htC ht hX htX hDe
  have hnn := not_normal_neighbour_anisoTorus_of_four_le hset hKc hq le_rfl hirr e htC ht hX hDe
  obtain ⟨-, -, -, -, -, hDC, hDq, -⟩ := neighbour_data_anisoTorus le_rfl hirr e htC hX hDe
  have hDm := lieModel_quotient_center_map_anisoPerp_four hKc hq hirr e hDe
  have hXne : X ≠ ⊥ := by
    intro hXb
    have h1 : Nat.card (anisoTorus (K := K) (n := 4) (by omega) b c) = Nat.card K + 1 :=
      card_anisoTorus le_rfl hirr
    have h2 : Nat.card X = Nat.card K + 1 := by
      rw [hX, ← h1]
      exact LinearPilot.card_map_symm e _
    rw [hXb, Subgroup.card_bot] at h2
    omega
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  exact LinearPilot.neighbour_overgroup_slm_center (by norm_num) (Or.inr hf2) hcat
    hset.standardSetting.kProper
    (F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple hset.standardSetting.nonab
      hXne) htX ht (hDC.trans inf_le_left) hDq hDm hcomp hsyl hstd hnn

theorem neighbour_overgroup_anisoTorus_four_field (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) {f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (n := 4) (by omega) b c).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (n := 4) (by omega) b c).map
      e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 4 f ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ := by
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting hset hKc le_rfl
    hirr e htC ht hX htX hDe
  obtain ⟨-, -, -, -, -, hDC, hDq, -⟩ := neighbour_data_anisoTorus le_rfl hirr e htC hX hDe
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  exact LinearPilot.NeighbourOvergroupSLm.field_oddCore htX ht (hDC.trans inf_le_left) hDq
    (by norm_num) (Or.inr hf2) hdet (lieModel_quotient_center_map_anisoPerp_four hKc hq hirr e hDe)
    hcomp (neighbour_overgroup_anisoTorus_four hset hcat hKc hq hirr e htC ht hX htX hDe)

theorem neighbourCore_anisoTorus_four (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (n := 4) (by omega) b c).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (n := 4) (by omega) b c).map
      e.symm.toMonoidHom).map L.subtype)
    (Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    (hKcomp : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hZK : center Kc = ⊥) (hmodel : LieModel Kc .PSL 4 2 (2 * f)) :
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
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting hset hKc le_rfl
    hirr e htC ht hX htX hDe
  obtain ⟨-, -, -, -, -, hDC, -, hZD⟩ := neighbour_data_anisoTorus le_rfl hirr e htC hX hDe
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_anisoTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_minus hset le_rfl hKc hirr e htC ht) le_rfl hirr e hX hDe
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

end CFSG.SeitzReduction.OmegaPilot
