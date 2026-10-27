module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIILocal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel

public section

namespace CFSG.ComponentClassification.RankTwoAlt.Six

open Equiv Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

theorem commutatorElement_mem_gammaE_psl {E : Subgroup P10} {e c d : P10} (he : e ∈ E)
    (he1 : e ≠ 1) (hc : code c ∈ Core.pslLit) (hd : code d ∈ Core.pslLit) (hce : c * e = e * c)
    (hde : d * e = e * d) : ⁅c, d⁆ ∈ gammaE A6Models.psl29 E := by
  have hle : centDer A6Models.psl29 e ≤ gammaE A6Models.psl29 E :=
    le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)
  exact hle (commutator_mem_commutator
    ⟨(mem_psl29_iff c).2 hc, mem_centralizer_singleton_iff.2 hce⟩
    ⟨(mem_psl29_iff d).2 hd, mem_centralizer_singleton_iff.2 hde⟩)

@[expose] def sixF0a : P10 := A6Models.perm10 [[3, 6], [4, 7], [5, 8]]

@[expose] def sixF0b : P10 := A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]]

theorem sixF0a_mem : sixF0a ∈ closure ({sixF0a, sixF0b} : Set P10) :=
  subset_closure (Set.mem_insert _ _)

theorem sixF0b_mem : sixF0b ∈ closure ({sixF0a, sixF0b} : Set P10) :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sixF0ab_mem : sixF0a * sixF0b ∈ closure ({sixF0a, sixF0b} : Set P10) :=
  mul_mem sixF0a_mem sixF0b_mem

theorem sixF0_tAdd_mem : A6Models.tAdd ∈ nE A6Models.psl29 (closure {sixF0a, sixF0b}) := by
  rw [show A6Models.tAdd = ⁅sixF0b, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 2, 9], [3, 7, 5], [4, 8, 6]]⁆⁆ * ⁅sixF0b, ⁅(A6Models.perm10 [[0, 2], [1, 9], [3, 6], [5, 8]] : P10), A6Models.perm10 [[0, 9], [3, 6], [4, 5], [7, 8]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixF0b_mem
        (commutatorElement_mem_gammaE_psl sixF0a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixF0b_mem
        (commutatorElement_mem_gammaE_psl sixF0a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

theorem sixF0_tSq_mem : A6Models.tSq ∈ nE A6Models.psl29 (closure {sixF0a, sixF0b}) := by
  rw [show A6Models.tSq = ⁅sixF0b, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 9], [3, 6], [4, 5], [7, 8]]⁆⁆ * ⁅sixF0b, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 5, 8], [2, 3, 6], [4, 9, 7]]⁆ * ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 9, 2, 1], [3, 8, 6, 5]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixF0b_mem
        (commutatorElement_mem_gammaE_psl sixF0a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixF0b_mem
        ((mul_mem (commutatorElement_mem_gammaE_psl sixF0ab_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_psl sixF0a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))))

theorem sixF0_tInv_mem : A6Models.tInv ∈ nE A6Models.psl29 (closure {sixF0a, sixF0b}) := by
  rw [show A6Models.tInv = ⁅sixF0b, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 9], [3, 6], [4, 5], [7, 8]]⁆⁆ * ⁅sixF0b, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 9, 2, 1], [3, 8, 6, 5]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixF0b_mem
        (commutatorElement_mem_gammaE_psl sixF0a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixF0b_mem
        (commutatorElement_mem_gammaE_psl sixF0a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))

theorem psl29_le_nE_sixF0 : A6Models.psl29 ≤ nE A6Models.psl29 (closure {sixF0a, sixF0b}) := by
  refine (le_of_eq psl29_eq).trans ?_
  rw [closure_le]
  intro g hg
  simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl | rfl
  · exact sixF0_tAdd_mem
  · exact sixF0_tSq_mem
  · exact sixF0_tInv_mem

@[expose] def sixF1a : P10 := A6Models.perm10 [[3, 6], [4, 7], [5, 8]]

@[expose] def sixF1b : P10 := A6Models.perm10 [[0, 1], [2, 9], [5, 8]]

theorem sixF1a_mem : sixF1a ∈ closure ({sixF1a, sixF1b} : Set P10) :=
  subset_closure (Set.mem_insert _ _)

theorem sixF1b_mem : sixF1b ∈ closure ({sixF1a, sixF1b} : Set P10) :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sixF1ab_mem : sixF1a * sixF1b ∈ closure ({sixF1a, sixF1b} : Set P10) :=
  mul_mem sixF1a_mem sixF1b_mem

theorem sixF1_tAdd_mem : A6Models.tAdd ∈ nE A6Models.psl29 (closure {sixF1a, sixF1b}) := by
  rw [show A6Models.tAdd = ⁅sixF1a, ⁅(A6Models.perm10 [[0, 2], [1, 9], [3, 6], [5, 8]] : P10), A6Models.perm10 [[0, 8, 2], [1, 5, 9], [3, 4, 7]]⁆⁆ * ⁅(sixF1a * sixF1b), ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 2, 9], [3, 7, 5], [4, 8, 6]]⁆ * ⁅(A6Models.perm10 [[0, 2], [1, 9], [3, 6], [5, 8]] : P10), A6Models.perm10 [[0, 8, 2], [1, 5, 9], [3, 4, 7]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixF1a_mem
        (commutatorElement_mem_gammaE_psl sixF1b_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixF1ab_mem
        ((mul_mem (commutatorElement_mem_gammaE_psl sixF1a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_psl sixF1b_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))))

theorem sixF1_tSq_mem : A6Models.tSq ∈ nE A6Models.psl29 (closure {sixF1a, sixF1b}) := by
  rw [show A6Models.tSq = ⁅sixF1b, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 2, 9], [3, 7, 5], [4, 8, 6]]⁆⁆ * ⁅(sixF1a * sixF1b), ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 2, 9], [3, 7, 5], [4, 8, 6]]⁆ * ⁅(A6Models.perm10 [[0, 2], [1, 9], [3, 6], [5, 8]] : P10), A6Models.perm10 [[0, 8, 2], [1, 5, 9], [3, 4, 7]]⁆ * ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 2, 9], [3, 7, 5], [4, 8, 6]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixF1b_mem
        (commutatorElement_mem_gammaE_psl sixF1a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixF1ab_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_psl sixF1a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_psl sixF1b_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_psl sixF1a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))))

theorem sixF1_tInv_mem : A6Models.tInv ∈ nE A6Models.psl29 (closure {sixF1a, sixF1b}) := by
  rw [show A6Models.tInv = ⁅sixF1b, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 9], [3, 6], [4, 5], [7, 8]]⁆⁆ by
    decide +kernel]
  exact RankTwoAlt.commutatorElement_mem_nE sixF1b_mem
        (commutatorElement_mem_gammaE_psl sixF1a_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem psl29_le_nE_sixF1 : A6Models.psl29 ≤ nE A6Models.psl29 (closure {sixF1a, sixF1b}) := by
  refine (le_of_eq psl29_eq).trans ?_
  rw [closure_le]
  intro g hg
  simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl | rfl
  · exact sixF1_tAdd_mem
  · exact sixF1_tSq_mem
  · exact sixF1_tInv_mem

@[expose] def sixPa : P10 := A6Models.perm10 [[0, 1], [2, 3], [4, 9], [5, 6], [7, 8]]

@[expose] def sixPb : P10 := A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]]

theorem sixPa_mem : sixPa ∈ closure ({sixPa, sixPb} : Set P10) :=
  subset_closure (Set.mem_insert _ _)

theorem sixPb_mem : sixPb ∈ closure ({sixPa, sixPb} : Set P10) :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sixPab_mem : sixPa * sixPb ∈ closure ({sixPa, sixPb} : Set P10) :=
  mul_mem sixPa_mem sixPb_mem

theorem sixP_tAdd_mem : A6Models.tAdd ∈ nE A6Models.psl29 (closure {sixPa, sixPb}) := by
  rw [show A6Models.tAdd = ⁅sixPb, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 8], [1, 7], [2, 6], [3, 5]]⁆⁆ * ⁅sixPa, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 3, 5, 8, 4], [1, 2, 6, 7, 9]]⁆ * ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 7], [1, 5], [3, 8], [6, 9]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixPb_mem
        (commutatorElement_mem_gammaE_psl sixPa_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixPa_mem
        ((mul_mem (commutatorElement_mem_gammaE_psl sixPa_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_psl sixPab_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))))

theorem sixP_tSq_mem : A6Models.tSq ∈ nE A6Models.psl29 (closure {sixPa, sixPb}) := by
  rw [show A6Models.tSq = ⁅sixPb, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 3, 5, 8, 4], [1, 2, 6, 7, 9]]⁆⁆ * ⁅(sixPa * sixPb), ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 3, 5, 8, 4], [1, 2, 6, 7, 9]]⁆ * ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 6], [1, 8], [2, 7], [4, 5]]⁆ * ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 3, 5, 8, 4], [1, 2, 6, 7, 9]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixPb_mem
        (commutatorElement_mem_gammaE_psl sixPa_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixPab_mem
        ((mul_mem ((mul_mem (commutatorElement_mem_gammaE_psl sixPa_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_psl sixPab_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))))
          (commutatorElement_mem_gammaE_psl sixPa_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))))

theorem sixP_tInv_mem : A6Models.tInv ∈ nE A6Models.psl29 (closure {sixPa, sixPb}) := by
  rw [show A6Models.tInv = ⁅sixPb, ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 5, 4, 3, 8], [1, 6, 9, 2, 7]]⁆⁆ * ⁅(sixPa * sixPb), ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 9], [1, 3], [2, 6], [4, 8]]⁆ * ⁅(A6Models.perm10 [[2, 9], [3, 4], [5, 8], [6, 7]] : P10), A6Models.perm10 [[0, 8], [1, 7], [2, 6], [3, 5]]⁆⁆ by
    decide +kernel]
  exact mul_mem (RankTwoAlt.commutatorElement_mem_nE sixPb_mem
        (commutatorElement_mem_gammaE_psl sixPa_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
      (RankTwoAlt.commutatorElement_mem_nE sixPab_mem
        ((mul_mem (commutatorElement_mem_gammaE_psl sixPab_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
          (commutatorElement_mem_gammaE_psl sixPa_mem (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))))

theorem psl29_le_nE_sixP : A6Models.psl29 ≤ nE A6Models.psl29 (closure {sixPa, sixPb}) := by
  refine (le_of_eq psl29_eq).trans ?_
  rw [closure_le]
  intro g hg
  simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl | rfl
  · exact sixP_tAdd_mem
  · exact sixP_tSq_mem
  · exact sixP_tInv_mem

end CFSG.ComponentClassification.RankTwoAlt.Six
