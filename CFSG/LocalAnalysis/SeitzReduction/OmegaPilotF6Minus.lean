module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] {n : ℕ}

noncomputable abbrev minusRadical (hn : 1 ≤ n) (b c : K) (i j : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  rootRadicalBar (coordinateQuadMinus n K hn b c) (isHypCoord_coordinateQuadMinus hn b c i).hypPair
    (isHypCoord_coordinateQuadMinus hn b c j).hypPair

noncomputable abbrev minusLevi (hn : 1 ≤ n) (b c : K) (i j : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  rootLeviBar (coordinateQuadMinus n K hn b c) (isHypCoord_coordinateQuadMinus hn b c i).hypPair
    (isHypCoord_coordinateQuadMinus hn b c j).hypPair

variable [Finite K] [CharP K 2]

theorem minusRootElt_decomp (hq : 4 ≤ Nat.card K) (hn : 6 ≤ n) {b c : K}
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
  have hS := isQuasisimple_minusStabPairsBar (K := K) hn hirr hij
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

theorem refinedF6_minusPairTorus (hq : 4 ≤ Nat.card K) (hn : 6 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    RefinedF6 (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j)
      (minusPairTorus (by omega) b c k) (minusPairPerp (K := K) (by omega) b c k) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  obtain ⟨g, h, hgh, hig, hih, hjg, hjh, hkg, hkh⟩ := exists_two_ne_three (by omega) i j k
  have hD : ⁅minusPairPerp (K := K) hn1 b c k, minusPairPerp (K := K) hn1 b c k⁆ =
      minusPairPerp (K := K) hn1 b c k :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_minusPairPerp (by omega) hirr k).1
  have hB4 := card_le_stabPairsBar_of_coords hQ hT
    (fun s : Fin (n - 1) ⊕ Fin (n - 1) => Sum.elim (fun m => minusIndexEquiv n hn1 (.inl m))
      (fun m => minusIndexEquiv n hn1 (.inr (.inl m))) s)
    (by
      rintro (x | x) (y | y) hxy <;>
        simp only [Sum.elim_inl, Sum.elim_inr, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
          Sum.inr.injEq, reduceCtorEq] at hxy <;> simp [hxy])
    (fun m => isHypCoord_coordinateQuadMinus hn1 b c m) hik hig hih hjk hjg hjh hkg hkh hgh
  exact refinedF6_pairTorusOf hQ hT hq (isHypCoord_coordinateQuadMinus hn1 b c i)
    (isHypCoord_coordinateQuadMinus hn1 b c j) hk (pairDisjoint_minus hn1 hij)
    (pairDisjoint_minus hn1 hik) (pairDisjoint_minus hn1 hjk)
    (isQuasisimple_minusStabPairsBar hn hirr hij) hB4 hD

end CFSG.SeitzReduction.OmegaPilot
