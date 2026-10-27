module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.Quasithin (perfectCore)

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem centralizer_longRoot_decomp_minus_of_four_le (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    ∃ (z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
      (Qz Mz : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))),
      z ∈ minusPairPerp (by omega) b c k ∧ IsLongRoot _ z ∧
        perfectCore (centralizer ({z} : Set _)) = centralizer {z} ∧
        centralizer {z} = Qz ⊔ Mz ∧ IsPGroup 2 Qz ∧
        Mz ≤ normalizer (Qz : Set (matrixProjectiveDerived
          (coordinateQuadMinus n K (by omega) b c))) ∧
        Disjoint Qz Mz ∧ (∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        minusPairTorus (by omega) b c k ≤ Mz := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n - 1) k
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hS := isQuasisimple_minusStabPairsBar_of_four_le (K := K) hn hirr hij
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, rootRadicalBar _ hi.hypPair hj.hypPair,
    rootLeviBar _ hi.hypPair hj.hypPair, ?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt_of hi hj hd hQ h₁₃ h₂₃ hl0 hl1
        (Subgroup.isPerfect_iff.mp hS.1.1)),
    centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of hi hj hd hQ hT hS N hN h2, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inr rfl)⟩

theorem minusRootElt_decomp_of_four_le (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
      z ∈ minusPairPerp (by omega) b c k ∧ IsLongRoot _ z ∧ z ≠ 1 ∧
      perfectCore (centralizer ({z} : Set (matrixProjectiveDerived
        (coordinateQuadMinus n K (by omega) b c)))) =
        minusRadical (by omega) b c i j ⊔ minusLevi (by omega) b c i j ∧
      IsPGroup 2 (minusRadical (K := K) (by omega) b c i j) ∧
      minusLevi (by omega) b c i j ≤ normalizer (minusRadical (by omega) b c i j :
        Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) ∧
      Disjoint (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j) ∧
      (∀ N : Subgroup (minusLevi (K := K) (by omega) b c i j), N.Normal → IsPGroup 2 N →
        N = ⊥) ∧
      minusPairTorus (by omega) b c k ≤ minusLevi (by omega) b c i j := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hS := isQuasisimple_minusStabPairsBar_of_four_le (K := K) hn hirr hij
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, ?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃,
    rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃, ?_, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of hi hj hd hQ hT hS N hN h2, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
  · rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt_of hi hj hd hQ h₁₃ h₂₃ hl0 hl1
        (Subgroup.isPerfect_iff.mp hS.1.1))]
    exact centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inr rfl)⟩

theorem refinedF6_minusPairTorus_of_four_le (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    RefinedF6 (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j)
      (minusPairTorus (by omega) b c k) (minusPairPerp (K := K) (by omega) b c k) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hD : ⁅minusPairPerp (K := K) hn1 b c k, minusPairPerp (K := K) hn1 b c k⁆ =
      minusPairPerp (K := K) hn1 b c k :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_minusPairPerp_of_four_le hn hirr k).1
  exact refinedF6_pairTorusOf hQ hT hq (isHypCoord_coordinateQuadMinus hn1 b c i)
    (isHypCoord_coordinateQuadMinus hn1 b c j) hk (pairDisjoint_minus hn1 hij)
    (pairDisjoint_minus hn1 hik) (pairDisjoint_minus hn1 hjk)
    (isQuasisimple_minusStabPairsBar_of_four_le hn hirr hij)
    (card_le_minusStabPairsBar_of_four_le hn hirr hij) hD

theorem refinedF6_anisoTorus_of_four_le (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) :
    RefinedF6 (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j)
      (anisoTorus (K := K) (n := n) (by omega) b c)
      (anisoPerp (K := K) (n := n) (by omega) b c) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hD : ⁅anisoPerp (K := K) hn1 b c, anisoPerp (K := K) hn1 b c⁆ =
      anisoPerp (K := K) hn1 b c :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_anisoPerp (by omega) hirr).1
  exact refinedF6_anisoTorusOf hQ hT (isHypCoord_coordinateQuadMinus hn1 b c i)
    (isHypCoord_coordinateQuadMinus hn1 b c j) (isAnisoCoord_coordinateQuadMinus hn1 hirr)
    (pairDisjoint_minus hn1 hij) (pairDisjoint_aniso hn1 i).symm (pairDisjoint_aniso hn1 j).symm
    (isQuasisimple_minusStabPairsBar_of_four_le hn hirr hij)
    (card_le_minusStabPairsBar_of_four_le hn hirr hij) hD

theorem minusRootElt_decomp_aniso_of_four_le (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
      z ∈ anisoPerp (by omega) b c ∧ IsLongRoot _ z ∧ z ≠ 1 ∧
      perfectCore (centralizer ({z} : Set (matrixProjectiveDerived
        (coordinateQuadMinus n K (by omega) b c)))) =
        minusRadical (by omega) b c i j ⊔ minusLevi (by omega) b c i j ∧
      IsPGroup 2 (minusRadical (K := K) (by omega) b c i j) ∧
      minusLevi (by omega) b c i j ≤ normalizer (minusRadical (by omega) b c i j :
        Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) ∧
      Disjoint (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j) ∧
      (∀ N : Subgroup (minusLevi (K := K) (by omega) b c i j), N.Normal → IsPGroup 2 N →
        N = ⊥) ∧
      anisoTorus (by omega) b c ≤ minusLevi (by omega) b c i j := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hS := isQuasisimple_minusStabPairsBar_of_four_le (K := K) hn hirr hij
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, rootPairElt_mem_anisoPerp (by omega) hirr hij hik hjk,
    isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃, rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃, ?_,
    isPGroup_rootRadicalBar _ _, rootLeviBar_le_normalizer h₁₂,
    disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of hi hj hd hQ hT hS N hN h2, ?_⟩
  · rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt_of hi hj hd hQ h₁₃ h₂₃ hl0 hl1
        (Subgroup.isPerfect_iff.mp hS.1.1))]
    exact centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  · exact (anisoTorusOf_le_stabPairsBar (anisoCoord_ne hn1) (pairDisjoint_aniso hn1 i).symm
      (pairDisjoint_aniso hn1 j).symm).trans (stabPairsBar_le_rootLeviBar hi hj)

end Main

end CFSG.SeitzReduction.OmegaPilot
