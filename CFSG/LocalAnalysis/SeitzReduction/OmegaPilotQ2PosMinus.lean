module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenHR5
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2Minus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.Quasithin (perfectCore)

section Model

variable {K : Type} [Field K] {n : ℕ}

noncomputable abbrev minusLeviTwo (hn : 1 ≤ n) (b c : K) (i j : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  stabPairsBar (coordinateQuadMinus n K hn b c) (minusIndexEquiv n hn (.inl i))
    (minusIndexEquiv n hn (.inr (.inl i))) (minusIndexEquiv n hn (.inl j))
    (minusIndexEquiv n hn (.inr (.inl j)))

variable [Finite K] [CharP K 2]

theorem minusRootElt_decomp_aniso_two (hK : Nat.card K = 2) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
      z ∈ anisoPerp (by omega) b c ∧ IsLongRoot _ z ∧ z ≠ 1 ∧
      perfectCore (centralizer ({z} : Set (matrixProjectiveDerived
        (coordinateQuadMinus n K (by omega) b c)))) =
        minusRadical (by omega) b c i j ⊔ minusLeviTwo (by omega) b c i j ∧
      IsPGroup 2 (minusRadical (K := K) (by omega) b c i j) ∧
      minusLeviTwo (by omega) b c i j ≤ normalizer (minusRadical (by omega) b c i j :
        Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) ∧
      Disjoint (minusRadical (K := K) (by omega) b c i j) (minusLeviTwo (by omega) b c i j) ∧
      (∀ N : Subgroup (minusLeviTwo (K := K) (by omega) b c i j), N.Normal → IsPGroup 2 N →
        N = ⊥) ∧
      anisoTorus (by omega) b c ≤ minusLeviTwo (by omega) b c i j := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, -⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  have hS := isQuasisimple_minusStabPairsBar_of_five_le (K := K) hn hirr hij
  obtain ⟨hQz, hMN, hQM, hM⟩ := rootRadicalBar_stabPairsBar_facts hi hj hd hS
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, rootPairElt_mem_anisoPerp (by omega) hirr hij hik hjk,
    isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃, rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃,
    perfectCore_centralizer_rootPairElt_two_of_aniso hK hQ hi hj hk
      (isAnisoCoord_coordinateQuadMinus hn1 hirr) hd (pairDisjoint_minus hn1 hik)
      (pairDisjoint_minus hn1 hjk) (pairDisjoint_aniso hn1 i).symm
      (pairDisjoint_aniso hn1 j).symm (pairDisjoint_aniso hn1 k).symm
      (Subgroup.isPerfect_iff.mp hS.1.1),
    hQz, hMN, hQM, hM, ?_⟩
  exact anisoTorusOf_le_stabPairsBar (anisoCoord_ne hn1) (pairDisjoint_aniso hn1 i).symm
    (pairDisjoint_aniso hn1 j).symm

theorem refinedF6_anisoTorus_two (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) :
    RefinedF6 (minusRadical (K := K) (by omega) b c i j) (minusLeviTwo (by omega) b c i j)
      (anisoTorus (K := K) (n := n) (by omega) b c)
      (anisoPerp (K := K) (n := n) (by omega) b c) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hD : ⁅anisoPerp (K := K) hn1 b c, anisoPerp (K := K) hn1 b c⁆ =
      anisoPerp (K := K) hn1 b c :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_anisoPerp (by omega) hirr).1
  exact refinedF6_anisoTorusOf_stabPairsBar hQ hT (isHypCoord_coordinateQuadMinus hn1 b c i)
    (isHypCoord_coordinateQuadMinus hn1 b c j) (isAnisoCoord_coordinateQuadMinus hn1 hirr)
    (pairDisjoint_minus hn1 hij) (pairDisjoint_aniso hn1 i).symm (pairDisjoint_aniso hn1 j).symm
    hD

end Model

section Group

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_anisoTorus_two (hset : SeitzSetting G L) {n : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X D : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  have hKt := inf_centralizer_eq_zpowers_minus hset (by omega) hKc hirr e htC ht
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩, hact⟩ :=
    exists_conj_eq_mul_longRoot_twoSided_minus_of_five_le hset hn hKc hirr e ht hKt
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n - 1) ⟨0, by omega⟩
  obtain ⟨z₀, hz₀D, hz₀L, hz₀1, hF3, hQz, hMN, hQM, hM, hJ⟩ :=
    minusRootElt_decomp_aniso_two hK2 hn hirr hij hik hjk
  have hF6 := refinedF6_anisoTorus_two (K := K) hn hirr hij
  obtain ⟨g, hg, w', hw', hact', hgw⟩ := exists_recentred_of_twoSided e htC hzL hzx hxz hact
    (isConj_of_isLongRoot_minus (by omega) hirr hzl hz₀L)
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
    exact isConj_of_isLongRoot_minus (by omega) hirr hzl' hz₀L
  have hOut := isSolvable_outer_of_mulEquiv_minus (by omega)
    (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc hirr e
  obtain ⟨P, hP, hPD⟩ := EPilot.exists_le_centralizer_mulEquiv_of_conj_eq_mul_single_of_isConj
    hset.standardSetting hOut e ht hKt hg ⟨w', hw', hact', hconj⟩ _ _ hF3 hQz hMN hQM hM hJ
    (odd_card_anisoTorus _ hirr) hF6
  obtain ⟨-, htX, -, -, -, hDC, hDq, hZD⟩ := neighbour_data_anisoTorus (by omega) hirr e htC hX hDe
  obtain ⟨-, hOutD⟩ := lieModel_map_anisoPerp hKc hn hirr e hDe
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting hset hKc (by omega) hirr e
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

end Group

theorem omegaMinusTwoPositionInput_holds : OmegaMinusTwoPositionInput := by
  intro G _ _ L hset n hn K _ _ _ b c hirr hK2 e t htC ht
  exact not_normal_neighbour_anisoTorus_two hset hK2 hn hirr e htC ht rfl rfl

theorem omegaMinusTwoInput_of_rows (h10 : OmegaMinusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m)
    (hfield : OmegaMinusTwoRowInput .field) (hswap : OmegaMinusTwoRowInput .swap) :
    OmegaMinusTwoInput :=
  omegaMinusTwoInput_of_inputs omegaMinusTwoPositionInput_holds h10 hcat hfield hswap

end CFSG.SeitzReduction.OmegaPilot
