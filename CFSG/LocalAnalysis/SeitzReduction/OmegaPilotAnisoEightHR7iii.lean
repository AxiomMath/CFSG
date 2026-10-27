module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.RankThree.PartOne.K159.Klein
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus coordinateQuadPlus
    regular_coordinateQuadPlus)

theorem isSolvable_outer_anisoPerp_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsSolvable (Outer (anisoPerp (K := K) (n := 4) (by omega) b c)) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (4 - 1) K (by omega)
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (coordinateQuadPlus (4 - 1) K) hQ (by rw [Module.finrank_fin_fun]) hT hq
  set O := TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus (4 - 1) K) with hO
  have h1 : (commutator ↥O).map O.subtype = orthDerived (coordinateQuadPlus (4 - 1) K) := by
    rw [Subgroup.map_subtype_commutator]
  let e₁ : orthDerived (coordinateQuadPlus (4 - 1) K) ≃* commutator ↥O :=
    ((Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)).symm
  let φ : anisoPerp (K := K) (n := 4) (by omega) b c ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
    (((anisoPerpEquiv le_rfl hirr).trans e₁).trans κ).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm
  have hsol := LinearPilot.isSolvable_outer_quotient_center_of_mulEquiv (m := 4) (by norm_num) φ
  have hcen := center_anisoPerp (K := K) (n := 4) le_rfl hirr
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)

theorem isSolvable_outer_map_anisoPerp_of_four_le {G : Type} [Group G] {L : Subgroup G}
    {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    Group.IsSolvable (Outer D) := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · subst hDe
    have := isSolvable_outer_anisoPerp_four hq hirr
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (LinearPilot.mapSymmMulEquiv e (anisoPerp (K := K) (n := 4) _ b c)).symm
  · exact (lieModel_map_anisoPerp hKc h5 hirr e hDe).2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_anisoTorus_of_four_le (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X D : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hKt := inf_centralizer_eq_zpowers_minus hset hn hKc hirr e htC ht
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩, hact⟩ :=
    exists_conj_eq_mul_longRoot_twoSided_minus hset hn hKc hq hirr e ht hKt
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n - 1) ⟨0, by omega⟩
  obtain ⟨z₀, hz₀D, hz₀L, hz₀1, hF3, hQz, hMN, hQM, hM, hJ⟩ :=
    minusRootElt_decomp_aniso_of_four_le hq hn hirr hij hik hjk
  have hF6 := refinedF6_anisoTorus_of_four_le (K := K) hn hirr hij
  obtain ⟨g, hg, w', hw', hact', hgw⟩ := exists_recentred_of_twoSided e htC hzL hzx hxz hact
    (isConj_of_isLongRoot_minus hn hirr hzl hz₀L)
  have hconj : IsConj (e ⟨g * w' * g⁻¹, hw'⟩) z₀ := by
    have hw : (⟨g * w' * g⁻¹, hw'⟩ : L) = (conjugateMulEquiv L x).symm ⟨z, hzx⟩ := by
      apply (conjugateMulEquiv L x).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [coe_conjugateMulEquiv]
      change x⁻¹ * (g * w' * g⁻¹) * x = z
      rw [hgw]
      group
    rw [hw]
    exact isConj_of_isLongRoot_minus hn hirr hzl' hz₀L
  have hOut := isSolvable_outer_of_mulEquiv_minus hn
    (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc hirr e
  obtain ⟨P, hP, hPD⟩ := EPilot.exists_le_centralizer_mulEquiv_of_conj_eq_mul_single_of_isConj
    hset.standardSetting hOut e ht hKt hg ⟨w', hw', hact', hconj⟩ _ _ hF3 hQz hMN hQM hM hJ
    (odd_card_anisoTorus _ hirr) hF6
  obtain ⟨-, htX, -, -, -, hDC, hDq, hZD⟩ := neighbour_data_anisoTorus hn hirr e htC hX hDe
  have hOutD := isSolvable_outer_map_anisoPerp_of_four_le hKc hq hn hirr e hDe
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting hset hKc hn hirr e
    htC ht hX htX hDe
  have hyD : (e.symm z₀ : G) ∈ D := by
    rw [hDe]
    exact ⟨e.symm z₀, ⟨z₀, hz₀D, rfl⟩, rfl⟩
  have hy1 : (e.symm z₀ : G) ≠ 1 := by
    intro h1
    have h2 : e.symm z₀ = 1 := Subtype.ext h1
    rw [MulEquiv.symm_apply_eq, map_one] at h2
    exact hz₀1 h2
  have hP' : P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm z₀ : G)} : Set G) := by
    rw [hX, ← hg]
    exact hP
  have hPD' : Nonempty (P ≃* D) := by
    obtain ⟨ePD⟩ := hPD
    subst hDe
    exact ⟨ePD.trans (LinearPilot.mapSymmMulEquiv e (anisoPerp (K := K) _ b c)).symm⟩
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht (hDC.trans inf_le_left)
    ⟨hDq.1.commutator_eq_top, hDq.2.1⟩ hZD hOutD (hDC.trans inf_le_right) hsyl hyD hy1
    (Or.inr rfl) hP' hPD'

end CFSG.SeitzReduction.OmegaPilot
