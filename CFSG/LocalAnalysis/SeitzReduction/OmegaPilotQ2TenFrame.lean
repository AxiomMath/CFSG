module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2Ten

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (plusIndexEquiv)

section Model

variable {K : Type} [Field K] {m : ℕ}

theorem isAnisoCoord_plusAnisoQuad₀_one [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsAnisoCoord (plusAnisoQuad₀ K m b c) (.inl 1) (.inr 1) b c where
  ne := Sum.inl_ne_inr
  map_left := by
    rw [plusAnisoQuad₀_apply]
    simp [(fin_one_ne_zero' (m := m)).symm, fin_succ_succ_ne_one]
  map_right := by
    rw [plusAnisoQuad₀_apply]
    simp [(fin_one_ne_zero' (m := m)).symm, fin_succ_succ_ne_one]
  polar_left v := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [QuadraticMap.polar, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply]
    simp [(fin_one_ne_zero' (m := m)).symm, fin_succ_succ_ne_one]
    linear_combination v (.inl 1) * h2
  polar_right v := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [QuadraticMap.polar, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply]
    simp [(fin_one_ne_zero' (m := m)).symm, fin_succ_succ_ne_one, mul_add]
    linear_combination c * v (.inr 1) * h2
  irr := hirr

theorem isAnisoCoord_plusAnisoQuad_one [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsAnisoCoord (plusAnisoQuad K m b c) (plusIndexEquiv (m + 2) (.inl 1))
      (plusIndexEquiv (m + 2) (.inr 1)) b c :=
  (isAnisoCoord_plusAnisoQuad₀_one hirr).reindex (plusIndexEquiv (m + 2))

theorem pairDisjoint_plusAniso_one :
    PairDisjoint (plusAnisoLeft m) (plusAnisoRight m) (plusIndexEquiv (m + 2) (.inl 1))
      (plusIndexEquiv (m + 2) (.inr 1)) where
  left_ne_left h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp only [Sum.inl.injEq] at this
    exact fin_one_ne_zero' this
  left_ne_right h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp at this
  right_ne_left h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp at this
  right_ne_right h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp only [Sum.inr.injEq] at this
    exact fin_one_ne_zero' this

theorem pairDisjoint_plusAniso_hyp_one (j : Fin m) :
    PairDisjoint (plusIndexEquiv (m + 2) (.inl j.succ.succ))
      (plusIndexEquiv (m + 2) (.inr j.succ.succ)) (plusIndexEquiv (m + 2) (.inl 1))
      (plusIndexEquiv (m + 2) (.inr 1)) where
  left_ne_left h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp only [Sum.inl.injEq] at this
    exact fin_succ_succ_ne_one j this.symm
  left_ne_right h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp at this
  right_ne_left h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp at this
  right_ne_right h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp only [Sum.inr.injEq] at this
    exact fin_succ_succ_ne_one j this.symm

end Model

section Frame

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem swapTriangleFrame_of_coords_aniso [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {u u' i i' j j' k k' l l' : Fin d} {c b' c' : K} (hW : IsAnisoCoord Q u u' 1 c)
    (hi : IsHypCoord Q i i') (hj : IsHypCoord Q j j') (hk : IsHypCoord Q k k')
    (hl : IsAnisoCoord Q l l' b' c')
    (dWI : PairDisjoint u u' i i') (dWJ : PairDisjoint u u' j j') (dWK : PairDisjoint u u' k k')
    (dWL : PairDisjoint u u' l l') (dIJ : PairDisjoint i i' j j') (dIK : PairDisjoint i i' k k')
    (dIL : PairDisjoint i i' l l') (dJK : PairDisjoint j j' k k') (dJL : PairDisjoint j j' l l')
    (dKL : PairDisjoint k k' l l')
    (hq : CFSG.IsQuasisimple (stabPairsBar Q i i' j j') ∧ center (stabPairsBar Q i i' j j') = ⊥) :
    SwapTriangleFrame (anisoTorusOf Q hW.ne 1 c) (pairPerpOf Q u u') := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := triPlanes_data hi hj dIJ c
  have mi := single_mem_perpSub (K := K) dWI.left_ne_left dWI.left_ne_right
  have mi' := single_mem_perpSub (K := K) dWI.right_ne_left dWI.right_ne_right
  have mj := single_mem_perpSub (K := K) dWJ.left_ne_left dWJ.left_ne_right
  have mj' := single_mem_perpSub (K := K) dWJ.right_ne_left dWJ.right_ne_right
  have hA : AnisoTriangleData Q u u' c (Pi.single i 1 + Pi.single i' 1)
      (Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1)
      (Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1) (Pi.single j 1 + c • Pi.single j' 1) :=
    ⟨add_mem mi mi', add_mem (add_mem mi' mj) (Submodule.smul_mem _ c mj'),
      add_mem (add_mem mi mi') mj', add_mem mj (Submodule.smul_mem _ c mj'),
      g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
  have ev : ∀ {x y : Fin d}, y ≠ x → (Pi.single x (1 : K) : Fin d → K) y = 0 :=
    fun h => Pi.single_eq_of_ne h 1
  have hpol : ∀ {a a' : Fin d}, IsHypCoord Q a a' → ∀ x : Fin d → K,
      polar Q x (Pi.single a 1) = x a' ∧ polar Q x (Pi.single a' 1) = x a := fun h x =>
    ⟨by rw [polar_comm, h.polar_left], by rw [polar_comm, h.polar_right]⟩
  refine swapTriangleFrame_of_planes hQ hT hW hA hk.hypPair (fun t s => ?_) (fun t s => ?_)
    (w := Pi.single l 1) (fun h => (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h l))
    (fun t s => ?_) ?_ ?_ (by rw [fixVecBar_triPlanes]; exact hq)
  · rw [IsHypCoord.hypPair_e, (hpol hk _).1]
    fin_cases t <;> cases s <;>
      simp [triVec, ev dIK.right_ne_left, ev dIK.right_ne_right, ev dJK.right_ne_left,
        ev dJK.right_ne_right, ev dWK.right_ne_left, ev dWK.right_ne_right]
  · rw [IsHypCoord.hypPair_f, (hpol hk _).2]
    fin_cases t <;> cases s <;>
      simp [triVec, ev dIK.left_ne_left, ev dIK.left_ne_right, ev dJK.left_ne_left,
        ev dJK.left_ne_right, ev dWK.left_ne_left, ev dWK.left_ne_right]
  · rw [polar_comm, hl.polar_left]
    fin_cases t <;> cases s <;>
      simp [triVec, ev dIL.right_ne_left, ev dIL.right_ne_right, ev dJL.right_ne_left,
        ev dJL.right_ne_right, ev dWL.right_ne_left, ev dWL.right_ne_right]
  · rw [IsHypCoord.hypPair_e, hk.polar_left]
    exact ev dKL.left_ne_right.symm
  · rw [IsHypCoord.hypPair_f, hk.polar_right]
    exact ev dKL.left_ne_left.symm

end Frame

section Ten

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem swapTriangleFrame_plusAnisoTorus_three {c : K} (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) :
    SwapTriangleFrame (plusAnisoTorus 3 hirr) (plusAnisoPerp (K := K) 3 1 c) := by
  obtain ⟨hQ, hT⟩ := regular_plusAnisoQuad (K := K) (m := 3) (b := 1) (c := c) one_ne_zero
    (by norm_num)
  exact swapTriangleFrame_of_coords_aniso hQ hT (isAnisoCoord_plusAnisoQuad hirr)
    (isHypCoord_plusAnisoQuad 1 c 0) (isHypCoord_plusAnisoQuad 1 c 1)
    (isHypCoord_plusAnisoQuad 1 c 2) (isAnisoCoord_plusAnisoQuad_one hirr)
    (pairDisjoint_plusAniso _) (pairDisjoint_plusAniso _) (pairDisjoint_plusAniso _)
    pairDisjoint_plusAniso_one (pairDisjoint_plusAniso_hyp (by decide))
    (pairDisjoint_plusAniso_hyp (by decide)) (pairDisjoint_plusAniso_hyp_one _)
    (pairDisjoint_plusAniso_hyp (by decide)) (pairDisjoint_plusAniso_hyp_one _)
    (pairDisjoint_plusAniso_hyp_one _)
    (isQuasisimple_stabPairsBar_plusAniso le_rfl hirr (by decide))

theorem omegaPlusTwoTenFrameInput_holds : OmegaPlusTwoTenFrameInput :=
  fun _ _ _ _ _ hirr _ => swapTriangleFrame_plusAnisoTorus_three hirr


theorem omegaPlusTwoTenInput_of_hr8_field (hHR8 : OmegaPlusTwoTenHR8Input)
    (hfield : OmegaPlusTwoTenFieldInput) : OmegaPlusTwoTenInput :=
  omegaPlusTwoTenInput_of_inputs hHR8 hfield omegaPlusTwoTenFrameInput_holds

end Ten

end CFSG.SeitzReduction.OmegaPilot
