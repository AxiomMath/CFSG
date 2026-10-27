module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEight
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_minusPairTorus_of_four_le (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n - 1)) {X D : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hKt := inf_centralizer_eq_zpowers_minus hset hn hKc hirr e htC ht
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩, hact⟩ :=
    exists_conj_eq_mul_longRoot_twoSided_minus hset hn hKc hq hirr e ht hKt
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n - 1) k
  obtain ⟨z₀, hz₀D, hz₀L, hz₀1, hF3, hQz, hMN, hQM, hM, hJ⟩ :=
    minusRootElt_decomp_of_four_le hq hn hirr hij hik hjk
  have hF6 := refinedF6_minusPairTorus_of_four_le hq hn hirr hij hik hjk
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
    (odd_card_minusPairTorus hKc (by omega) b c k) hF6
  obtain ⟨-, htX, -, -, -, -, hDC, hDq, hZD, hOutD⟩ :=
    neighbour_data_minusPairTorus_of_four_le hKc hq hn hirr k e htC hX hDe
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le hset hKc hq
    hn hirr k e htC ht hX htX hDe
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
    exact ⟨ePD.trans (LinearPilot.mapSymmMulEquiv e (minusPairPerp (K := K) _ b c k)).symm⟩
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht (hDC.trans inf_le_left)
    ⟨hDq.1.commutator_eq_top, hDq.2.1⟩ hZD hOutD (hDC.trans inf_le_right) hsyl hyD hy1
    (Or.inr rfl) hP' hPD'

end CFSG.SeitzReduction.OmegaPilot
