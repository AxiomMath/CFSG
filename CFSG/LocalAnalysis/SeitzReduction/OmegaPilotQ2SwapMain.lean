module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapCoord
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadMinus minusIndexEquiv
    plusIndexEquiv)

theorem eq_one_of_ne_zero_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {x : K} (hx : x ≠ 0) : x = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [Fintype.card_eq_nat_card, hK, _root_.sq] at h
  exact mul_left_cancel₀ hx (by rw [h, mul_one])

theorem fin_mk_ne {k a b : ℕ} (ha : a < k) (hb : b < k) (h : a ≠ b) :
    (⟨a, ha⟩ : Fin k) ≠ ⟨b, hb⟩ :=
  fun e => h (Fin.mk.inj_iff.1 e)

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem swapTriangleFrame_anisoTorus (hn : 5 ≤ n) {c : K}
    (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) :
    SwapTriangleFrame (anisoTorus (K := K) (by omega : 1 ≤ n) 1 c)
      (anisoPerp (K := K) (by omega : 1 ≤ n) 1 c) := by
  have h1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K 1 c (by omega) hirr
  have d01 := pairDisjoint_minus h1 (fin_mk_ne (k := n - 1) (a := 0) (b := 1) (by omega)
    (by omega) (by decide))
  have d02 := pairDisjoint_minus h1 (fin_mk_ne (k := n - 1) (a := 0) (b := 2) (by omega)
    (by omega) (by decide))
  have d03 := pairDisjoint_minus h1 (fin_mk_ne (k := n - 1) (a := 0) (b := 3) (by omega)
    (by omega) (by decide))
  have d12 := pairDisjoint_minus h1 (fin_mk_ne (k := n - 1) (a := 1) (b := 2) (by omega)
    (by omega) (by decide))
  have d13 := pairDisjoint_minus h1 (fin_mk_ne (k := n - 1) (a := 1) (b := 3) (by omega)
    (by omega) (by decide))
  have d23 := pairDisjoint_minus h1 (fin_mk_ne (k := n - 1) (a := 2) (b := 3) (by omega)
    (by omega) (by decide))
  exact swapTriangleFrame_of_coords hQ hT (isAnisoCoord_coordinateQuadMinus h1 hirr)
    (isHypCoord_coordinateQuadMinus h1 1 c ⟨0, by omega⟩)
    (isHypCoord_coordinateQuadMinus h1 1 c ⟨1, by omega⟩)
    (isHypCoord_coordinateQuadMinus h1 1 c ⟨2, by omega⟩)
    (isHypCoord_coordinateQuadMinus h1 1 c ⟨3, by omega⟩)
    (pairDisjoint_aniso h1 _) (pairDisjoint_aniso h1 _) (pairDisjoint_aniso h1 _)
    (pairDisjoint_aniso h1 _) d01 d02 d03 d12 d13 d23
    (isQuasisimple_minusStabPairsBar_of_four_le (by omega) hirr
      (fin_mk_ne (k := n - 1) (a := 0) (b := 1) (by omega) (by omega) (by decide)))

end Minus

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem swapTriangleFrame_plusAnisoTorus (hm : 4 ≤ m) {c : K}
    (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) :
    SwapTriangleFrame (plusAnisoTorus m hirr) (plusAnisoPerp (K := K) m 1 c) := by
  obtain ⟨hQ, hT⟩ := regular_plusAnisoQuad (K := K) (b := 1) (c := c) one_ne_zero
    (by omega : 1 ≤ m)
  have d01 := pairDisjoint_plusAniso_hyp (fin_mk_ne (k := m) (a := 0) (b := 1) (by omega)
    (by omega) (by decide))
  have d02 := pairDisjoint_plusAniso_hyp (fin_mk_ne (k := m) (a := 0) (b := 2) (by omega)
    (by omega) (by decide))
  have d03 := pairDisjoint_plusAniso_hyp (fin_mk_ne (k := m) (a := 0) (b := 3) (by omega)
    (by omega) (by decide))
  have d12 := pairDisjoint_plusAniso_hyp (fin_mk_ne (k := m) (a := 1) (b := 2) (by omega)
    (by omega) (by decide))
  have d13 := pairDisjoint_plusAniso_hyp (fin_mk_ne (k := m) (a := 1) (b := 3) (by omega)
    (by omega) (by decide))
  have d23 := pairDisjoint_plusAniso_hyp (fin_mk_ne (k := m) (a := 2) (b := 3) (by omega)
    (by omega) (by decide))
  exact swapTriangleFrame_of_coords hQ hT (isAnisoCoord_plusAnisoQuad hirr)
    (isHypCoord_plusAnisoQuad 1 c ⟨0, by omega⟩) (isHypCoord_plusAnisoQuad 1 c ⟨1, by omega⟩)
    (isHypCoord_plusAnisoQuad 1 c ⟨2, by omega⟩) (isHypCoord_plusAnisoQuad 1 c ⟨3, by omega⟩)
    (pairDisjoint_plusAniso _) (pairDisjoint_plusAniso _) (pairDisjoint_plusAniso _)
    (pairDisjoint_plusAniso _) d01 d02 d03 d12 d13 d23
    (isQuasisimple_stabPairsBar_plusAniso (by omega) hirr
      (fin_mk_ne (k := m) (a := 0) (b := 1) (by omega) (by omega) (by decide)))

end Plus

section Rows


theorem omegaMinusTwoRowInput_swap : OmegaMinusTwoRowInput .swap := by
  refine omegaMinusTwoRowInput_swap_of_frame fun n hn K _ _ _ b c hirr hK2 => ?_
  obtain rfl : b = 1 := eq_one_of_ne_zero_of_card_two hK2 (coeff_ne_zero_of_irreducible' hirr)
  exact swapTriangleFrame_anisoTorus (by omega) hirr

theorem omegaPlusTwoRowInput_swap : OmegaPlusTwoRowInput .swap := by
  refine omegaPlusTwoRowInput_swap_of_frame fun m hm K _ _ _ b c hirr hK2 => ?_
  obtain rfl : b = 1 := eq_one_of_ne_zero_of_card_two hK2 (coeff_ne_zero_of_irreducible' hirr)
  exact swapTriangleFrame_plusAnisoTorus hm hirr

end Rows

end CFSG.SeitzReduction.OmegaPilot
