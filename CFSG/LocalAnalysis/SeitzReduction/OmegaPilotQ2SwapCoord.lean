module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapTri

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ClassicalGroups.Orthogonal
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Coord

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {i i' j j' : Fin d}

theorem triPlanes_data (hi : IsHypCoord Q i i') (hj : IsHypCoord Q j j')
    (hd : PairDisjoint i i' j j') (c : K) :
    Q (Pi.single i 1 + Pi.single i' 1) = 1 ∧
    Q (Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1) = c ∧
    Q (Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1) = 1 ∧
    Q (Pi.single j 1 + c • Pi.single j' 1) = c ∧
    polar Q (Pi.single i 1 + Pi.single i' 1) (Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1)
      = 1 ∧
    polar Q (Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1) (Pi.single j 1 + c • Pi.single j' 1)
      = 1 ∧
    polar Q (Pi.single i 1 + Pi.single i' 1) (Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1) = 0 ∧
    polar Q (Pi.single i 1 + Pi.single i' 1) (Pi.single j 1 + c • Pi.single j' 1) = 0 ∧
    polar Q (Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1)
      (Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1) = 0 ∧
    polar Q (Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1)
      (Pi.single j 1 + c • Pi.single j' 1) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : (Pi.single i (1 : K) : Fin d → K) i' = 0 := Pi.single_eq_of_ne hi.ne.symm 1
  have e2 : (Pi.single i' (1 : K) : Fin d → K) i = 0 := Pi.single_eq_of_ne hi.ne 1
  have e3 : (Pi.single j (1 : K) : Fin d → K) j' = 0 := Pi.single_eq_of_ne hj.ne.symm 1
  have e4 : (Pi.single j' (1 : K) : Fin d → K) j = 0 := Pi.single_eq_of_ne hj.ne 1
  have e5 : (Pi.single i (1 : K) : Fin d → K) j = 0 := Pi.single_eq_of_ne hd.left_ne_left 1
  have e6 : (Pi.single i (1 : K) : Fin d → K) j' = 0 := Pi.single_eq_of_ne hd.right_ne_left 1
  have e7 : (Pi.single i' (1 : K) : Fin d → K) j = 0 := Pi.single_eq_of_ne hd.left_ne_right 1
  have e8 : (Pi.single i' (1 : K) : Fin d → K) j' = 0 := Pi.single_eq_of_ne hd.right_ne_right 1
  have e9 : (Pi.single j (1 : K) : Fin d → K) i = 0 := Pi.single_eq_of_ne hd.left_ne_left.symm 1
  have e10 : (Pi.single j (1 : K) : Fin d → K) i' = 0 := Pi.single_eq_of_ne hd.left_ne_right.symm 1
  have e11 : (Pi.single j' (1 : K) : Fin d → K) i = 0 := Pi.single_eq_of_ne hd.right_ne_left.symm 1
  have e12 : (Pi.single j' (1 : K) : Fin d → K) i' = 0 :=
    Pi.single_eq_of_ne hd.right_ne_right.symm 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_add_left, polar_add_right,
      polar_smul_left, polar_smul_right, hi.map_left, hi.map_right, hj.map_left, hj.map_right,
      hi.polar_left, hi.polar_right, hj.polar_left, hj.polar_right, Pi.smul_apply,
      Pi.single_eq_same, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, smul_eq_mul, mul_zero,
      mul_one, zero_add, add_zero]
  all_goals first
    | linear_combination (0 : K) * h2
    | linear_combination h2
    | linear_combination c * h2

theorem fixVecBar_triPlanes (c : K) :
    fixVecBar Q {Pi.single i 1 + Pi.single i' 1,
        Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1,
        Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1, Pi.single j 1 + c • Pi.single j' 1} =
      stabPairsBar Q i i' j j' := by
  rw [stabPairsBar_eq_fixVecBar]
  have h : fixVecSub (K := K) {Pi.single i 1 + Pi.single i' 1,
      Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1,
      Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1, Pi.single j 1 + c • Pi.single j' 1} =
      fixVecSub {Pi.single i 1, Pi.single i' 1, Pi.single j 1, Pi.single j' 1} := by
    set p : Fin d → K := Pi.single i 1 + Pi.single i' 1
    set p' : Fin d → K := Pi.single i' 1 + Pi.single j 1 + c • Pi.single j' 1
    set r : Fin d → K := Pi.single i 1 + Pi.single i' 1 + Pi.single j' 1
    set r' : Fin d → K := Pi.single j 1 + c • Pi.single j' 1
    apply le_antisymm
    · apply fixVecSub_le_of_subset_span
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      have hp : p ∈ Submodule.span K ({p, p', r, r'} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      have hp' : p' ∈ Submodule.span K ({p, p', r, r'} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      have hr : r ∈ Submodule.span K ({p, p', r, r'} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      have hr' : r' ∈ Submodule.span K ({p, p', r, r'} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (Pi.single i 1 : Fin d → K) = p - p' + r' by simp only [p, p', r']; module]
        exact add_mem (sub_mem hp hp') hr'
      · rw [show (Pi.single i' 1 : Fin d → K) = p' - r' by simp only [p', r']; module]
        exact sub_mem hp' hr'
      · rw [show (Pi.single j 1 : Fin d → K) = r' - c • (r - p) by simp only [p, r, r']; module]
        exact sub_mem hr' (Submodule.smul_mem _ c (sub_mem hr hp))
      · rw [show (Pi.single j' 1 : Fin d → K) = r - p by simp only [p, r]; module]
        exact sub_mem hr hp
    · apply fixVecSub_le_of_subset_span
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      have hi : (Pi.single i 1 : Fin d → K) ∈ Submodule.span K
          ({Pi.single i 1, Pi.single i' 1, Pi.single j 1, Pi.single j' 1} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      have hi' : (Pi.single i' 1 : Fin d → K) ∈ Submodule.span K
          ({Pi.single i 1, Pi.single i' 1, Pi.single j 1, Pi.single j' 1} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      have hj : (Pi.single j 1 : Fin d → K) ∈ Submodule.span K
          ({Pi.single i 1, Pi.single i' 1, Pi.single j 1, Pi.single j' 1} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      have hj' : (Pi.single j' 1 : Fin d → K) ∈ Submodule.span K
          ({Pi.single i 1, Pi.single i' 1, Pi.single j 1, Pi.single j' 1} : Set (Fin d → K)) :=
        Submodule.subset_span (by simp)
      exact ⟨add_mem hi hi', add_mem (add_mem hi' hj) (Submodule.smul_mem _ c hj'),
        add_mem (add_mem hi hi') hj', add_mem hj (Submodule.smul_mem _ c hj')⟩
  rw [fixVecBar, fixVecBar, h]

theorem swapTriangleFrame_of_coords [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {u u' k k' l l' : Fin d} {c : K} (hW : IsAnisoCoord Q u u' 1 c) (hi : IsHypCoord Q i i')
    (hj : IsHypCoord Q j j') (hk : IsHypCoord Q k k') (hl : IsHypCoord Q l l')
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
    (fun t s => ?_)
    ?_ ?_ (by rw [fixVecBar_triPlanes]; exact hq)
  · rw [IsHypCoord.hypPair_e, (hpol hk _).1]
    fin_cases t <;> cases s <;>
      simp [triVec, ev dIK.right_ne_left, ev dIK.right_ne_right, ev dJK.right_ne_left,
        ev dJK.right_ne_right, ev dWK.right_ne_left, ev dWK.right_ne_right]
  · rw [IsHypCoord.hypPair_f, (hpol hk _).2]
    fin_cases t <;> cases s <;>
      simp [triVec, ev dIK.left_ne_left, ev dIK.left_ne_right, ev dJK.left_ne_left,
        ev dJK.left_ne_right, ev dWK.left_ne_left, ev dWK.left_ne_right]
  · rw [(hpol hl _).1]
    fin_cases t <;> cases s <;>
      simp [triVec, ev dIL.right_ne_left, ev dIL.right_ne_right, ev dJL.right_ne_left,
        ev dJL.right_ne_right, ev dWL.right_ne_left, ev dWL.right_ne_right]
  · rw [IsHypCoord.hypPair_e, hk.polar_left]
    exact ev dKL.left_ne_right.symm
  · rw [IsHypCoord.hypPair_f, hk.polar_right]
    exact ev dKL.left_ne_left.symm

end Coord

end CFSG.SeitzReduction.OmegaPilot
