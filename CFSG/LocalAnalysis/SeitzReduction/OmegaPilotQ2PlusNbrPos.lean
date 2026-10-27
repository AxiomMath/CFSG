module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrStd
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (plusIndexEquiv coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)

section Model

variable {K : Type} [Field K] {m : ℕ}

variable (K m) in
noncomputable abbrev plusAnisoRadical [CharP K 2] (b c : K) (j₁ j₂ : Fin m) :
    Subgroup (matrixProjectiveDerived (plusAnisoQuad K m b c)) :=
  rootRadicalBar (plusAnisoQuad K m b c) (isHypCoord_plusAnisoQuad b c j₁).hypPair
    (isHypCoord_plusAnisoQuad b c j₂).hypPair

variable (K m) in
noncomputable abbrev plusAnisoLeviTwo (b c : K) (j₁ j₂ : Fin m) :
    Subgroup (matrixProjectiveDerived (plusAnisoQuad K m b c)) :=
  stabPairsBar (plusAnisoQuad K m b c) (plusIndexEquiv (m + 2) (.inl j₁.succ.succ))
    (plusIndexEquiv (m + 2) (.inr j₁.succ.succ)) (plusIndexEquiv (m + 2) (.inl j₂.succ.succ))
    (plusIndexEquiv (m + 2) (.inr j₂.succ.succ))

variable [Finite K] [CharP K 2]

theorem plusRootElt_decomp_aniso_two (hK : Nat.card K = 2) (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {j₁ j₂ j₃ : Fin m} (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃)
    (h23 : j₂ ≠ j₃) :
    ∃ z : matrixProjectiveDerived (plusAnisoQuad K m b c),
      z ∈ plusAnisoPerp m b c ∧ IsLongRoot _ (plusAnisoProjEquiv m hirr z) ∧ z ≠ 1 ∧
      perfectCore (centralizer ({z} : Set (matrixProjectiveDerived (plusAnisoQuad K m b c)))) =
        plusAnisoRadical K m b c j₁ j₂ ⊔ plusAnisoLeviTwo K m b c j₁ j₂ ∧
      IsPGroup 2 (plusAnisoRadical K m b c j₁ j₂) ∧
      plusAnisoLeviTwo K m b c j₁ j₂ ≤ normalizer (plusAnisoRadical K m b c j₁ j₂ :
        Set (matrixProjectiveDerived (plusAnisoQuad K m b c))) ∧
      Disjoint (plusAnisoRadical K m b c j₁ j₂) (plusAnisoLeviTwo K m b c j₁ j₂) ∧
      (∀ N : Subgroup (plusAnisoLeviTwo K m b c j₁ j₂), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      plusAnisoTorus m hirr ≤ plusAnisoLeviTwo K m b c j₁ j₂ := by
  have hb := coeff_ne_zero_of_irreducible' hirr
  obtain ⟨hQ, -⟩ := regular_plusAnisoQuad (K := K) (b := b) (c := c) hb (by omega : 1 ≤ m)
  have hi := isHypCoord_plusAnisoQuad (K := K) (m := m) b c j₁
  have hj := isHypCoord_plusAnisoQuad (K := K) (m := m) b c j₂
  have hk := isHypCoord_plusAnisoQuad (K := K) (m := m) b c j₃
  have hd := pairDisjoint_plusAniso_hyp h12
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_plusAniso_hyp h13)
  have h₂₃ := hj.orth hk (pairDisjoint_plusAniso_hyp h23)
  have hS := isQuasisimple_stabPairsBar_plusAniso hm hirr h12
  have hu := isAnisoCoord_plusAnisoQuad (m := m) hirr
  have d₁ := pairDisjoint_plusAniso (m := m) j₁
  have d₂ := pairDisjoint_plusAniso (m := m) j₂
  obtain ⟨hQz, hMN, hQM, hM⟩ := rootRadicalBar_stabPairsBar_facts hi hj hd hS
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, ?_, ?_, rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃,
    perfectCore_centralizer_rootPairElt_two_of_aniso hK hQ hi hj hk hu hd
      (pairDisjoint_plusAniso_hyp h13) (pairDisjoint_plusAniso_hyp h23) d₁.symm d₂.symm
      (pairDisjoint_plusAniso j₃).symm (Subgroup.isPerfect_iff.mp hS.1.1),
    hQz, hMN, hQM, hM, anisoTorusOf_le_stabPairsBar hu.ne d₁.symm d₂.symm⟩
  · refine ⟨_, mem_subgroupOf.mpr ⟨eichler_apply_of_polar_eq_zero ?_ ?_,
      eichler_apply_of_polar_eq_zero ?_ ?_⟩, rfl⟩
    · change polar _ (Pi.single (plusAnisoLeft m) 1)
        (Pi.single (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) 1) = 0
      rw [hu.polar_left, Pi.single_eq_of_ne d₁.left_ne_right.symm, mul_zero]
    · change polar _ (Pi.single (plusAnisoLeft m) 1)
        (Pi.single (plusIndexEquiv (m + 2) (.inl j₂.succ.succ)) 1) = 0
      rw [hu.polar_left, Pi.single_eq_of_ne d₂.left_ne_right.symm, mul_zero]
    · change polar _ (Pi.single (plusAnisoRight m) 1)
        (Pi.single (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) 1) = 0
      rw [hu.polar_right, Pi.single_eq_of_ne d₁.left_ne_left.symm, mul_zero]
    · change polar _ (Pi.single (plusAnisoRight m) 1)
        (Pi.single (plusIndexEquiv (m + 2) (.inl j₂.succ.succ)) 1) = 0
      rw [hu.polar_right, Pi.single_eq_of_ne d₂.left_ne_left.symm, mul_zero]
  · rw [plusAnisoProjEquiv_rootPairElt hirr (by omega) h12 h13 h23]
    exact isLongRoot_rootPairElt _ _ _ _

theorem refinedF6_plusAnisoTorus_two (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {j₁ j₂ : Fin m} (h12 : j₁ ≠ j₂) :
    RefinedF6 (plusAnisoRadical K m b c j₁ j₂) (plusAnisoLeviTwo K m b c j₁ j₂)
      (plusAnisoTorus m hirr) (plusAnisoPerp (K := K) m b c) := by
  obtain ⟨hQ, hT⟩ := regular_plusAnisoQuad (K := K) (b := b) (c := c)
    (coeff_ne_zero_of_irreducible' hirr) (by omega : 1 ≤ m)
  exact refinedF6_anisoTorusOf_stabPairsBar hQ hT (isHypCoord_plusAnisoQuad b c j₁)
    (isHypCoord_plusAnisoQuad b c j₂) (isAnisoCoord_plusAnisoQuad hirr)
    (pairDisjoint_plusAniso_hyp h12) (pairDisjoint_plusAniso j₁).symm
    (pairDisjoint_plusAniso j₂).symm
    (Subgroup.isPerfect_iff.mp (isQuasisimple_plusAnisoPerp hm hirr).1)

end Model

section Group

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_plusAnisoTorus_two (hset : SeitzSetting G L) {m : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X D : Subgroup G}
    (hX : X = ((plusAnisoTorus m hirr).map
      (e.trans (plusAnisoProjEquiv m hirr).symm).symm.toMonoidHom).map L.subtype)
    (hDe : D = ((plusAnisoPerp (K := K) m b c).map
      (e.trans (plusAnisoProjEquiv m hirr).symm).symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  set e' := e.trans (plusAnisoProjEquiv m hirr).symm with he'
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  have hn : 5 ≤ m + 2 := by omega
  have hKt := inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩, hact⟩ :=
    exists_conj_eq_mul_longRoot_twoSided_plus_of_habel_of_five_le hset hn hKc e ht hKt
      (habel_plus_of_odd hset hn odd_one hKc e ht hKt)
  obtain ⟨j₁, j₂, h12, h13, h23⟩ := exists_pair_ne_fin (by omega : 3 ≤ m) ⟨0, by omega⟩
  obtain ⟨z₀, hz₀D, hz₀L, hz₀1, hF3, hQz, hMN, hQM, hM, hJ⟩ :=
    plusRootElt_decomp_aniso_two hK2 hm hirr h12 h13 h23
  have hF6 := refinedF6_plusAnisoTorus_two hm hirr h12
  have hc1 : IsConj (e' ⟨z, hzL⟩) z₀ := by
    have h := (plusAnisoProjEquiv m hirr).symm.toMonoidHom.map_isConj
      (isConj_of_isLongRoot_plus (by omega) hzl hz₀L)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
    exact h
  obtain ⟨g, hg, w', hw', hact', hgw⟩ := exists_recentred_of_twoSided e' htC hzL hzx hxz hact hc1
  have hconj : IsConj (e' ⟨g * w' * g⁻¹, hw'⟩) z₀ := by
    have hw : (⟨g * w' * g⁻¹, hw'⟩ : L) = (conjugateMulEquiv L x).symm ⟨z, hzx⟩ := by
      apply (conjugateMulEquiv L x).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [coe_conjugateMulEquiv]
      change x⁻¹ * (g * w' * g⁻¹) * x = z
      rw [hgw]
      group
    have hzl'' : IsLongRoot _ (e ⟨g * w' * g⁻¹, hw'⟩) := by
      rw [hw]
      exact hzl'
    have h := (plusAnisoProjEquiv m hirr).symm.toMonoidHom.map_isConj
      (isConj_of_isLongRoot_plus (by omega) hzl'' hz₀L)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
    exact h
  have hOut := isSolvable_outer_of_mulEquiv_plus (by omega)
    (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc e
  obtain ⟨P, hP, hPD⟩ := EPilot.exists_le_centralizer_mulEquiv_of_conj_eq_mul_single_of_isConj
    hset.standardSetting hOut e' ht hKt hg ⟨w', hw', hact', hconj⟩ _ _ hF3 hQz hMN hQM hM hJ
    (plusAnisoTorus_facts hirr).1 hF6
  obtain ⟨-, htX, -, -, -, hDC, hDq, hZD⟩ := neighbour_data_plusAnisoTorus hm hirr e' htC hX hDe
  obtain ⟨-, hOutD⟩ := lieModel_map_plusAnisoPerp hKc hm hirr e' hDe
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_plusAnisoTorus hset.standardSetting.standard htC ht
    hKt hm hirr e' hX htX hDe
  have hyD : (e'.symm z₀ : G) ∈ D := by
    rw [hDe]
    exact ⟨e'.symm z₀, ⟨z₀, hz₀D, rfl⟩, rfl⟩
  have hy1 : (e'.symm z₀ : G) ≠ 1 := by
    intro h1
    have h2 : e'.symm z₀ = 1 := Subtype.ext h1
    rw [MulEquiv.symm_apply_eq, map_one] at h2
    exact hz₀1 h2
  have hP' : P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e'.symm z₀ : G)} : Set G) := by
    rw [hX, ← hg]
    exact hP
  have hPD' : Nonempty (P ≃* D) := by
    obtain ⟨ePD⟩ := hPD
    subst hDe
    exact ⟨ePD.trans (LinearPilot.mapSymmMulEquiv e' (plusAnisoPerp (K := K) m b c)).symm⟩
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht (hDC.trans inf_le_left)
    ⟨hDq.1.commutator_eq_top, hDq.2.1⟩ hZD hOutD (hDC.trans inf_le_right) hsyl hyD hy1
    (Or.inr rfl) hP' hPD'

end Group

end CFSG.SeitzReduction.OmegaPilot
