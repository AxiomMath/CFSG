module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Timmesfeld.Torality.E8ChainTab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three4
public import CFSG.RankThree.PartOne.KE6.E8T3Data

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Certs


@[expose] def e8A2Beta : Fin Tag.E8.rank → ℤ := toVec Tag.E8.rank [0, 1, 1, 2, 2, 2, 1, 1]

@[expose] def e8A2NegBeta : Fin Tag.E8.rank → ℤ :=
  toVec Tag.E8.rank [0, -1, -1, -2, -2, -2, -1, -1]

@[expose] def e8A2Delta : Fin Tag.E8.rank → ℤ :=
  toVec Tag.E8.rank [-1, -1, -1, -2, -2, -2, -1, -1]

@[expose] def e8A2Gamma : Fin Tag.E8.rank → ℤ := toVec Tag.E8.rank [1, 1, 1, 2, 2, 2, 1, 1]

@[expose] def e8A2RootsB (α : Fin Tag.E8.rank → ℤ) : Bool :=
  decide (α = Pi.single (0 : Fin Tag.E8.rank) 1) ||
  decide (α = -Pi.single (0 : Fin Tag.E8.rank) 1) ||
  decide (α = e8A2Beta) || decide (α = e8A2NegBeta) ||
  decide (α = e8A2Delta) || decide (α = e8A2Gamma)

theorem e8A2Beta_lit :
    (![0, 1, 1, 2, 2, 2, 1, 1] : Fin Tag.E8.rank → ℤ) = e8A2Beta := by
  funext i; fin_cases i <;> rfl

theorem e8A2NegBeta_lit :
    (-![0, 1, 1, 2, 2, 2, 1, 1] : Fin Tag.E8.rank → ℤ) = e8A2NegBeta := by
  funext i; fin_cases i <;> rfl

theorem e8A2NegBeta_eq_neg : e8A2NegBeta = -e8A2Beta := by
  funext i; fin_cases i <;> rfl

theorem e8A2Delta_lit :
    (![-1, -1, -1, -2, -2, -2, -1, -1] : Fin Tag.E8.rank → ℤ) = e8A2Delta := by
  funext i; fin_cases i <;> rfl

theorem e8A2Gamma_lit :
    (-![-1, -1, -1, -2, -2, -2, -1, -1] : Fin Tag.E8.rank → ℤ) = e8A2Gamma := by
  funext i; fin_cases i <;> rfl

theorem e8A2Gamma_eq_neg_delta :
    e8A2Gamma = -e8A2Delta := by
  funext i; fin_cases i <;> rfl

theorem e8A2Roots_explicit :
    e8A2Roots = {α : Fin Tag.E8.rank → ℤ |
      α = Pi.single (0 : Fin Tag.E8.rank) 1 ∨ α = -Pi.single (0 : Fin Tag.E8.rank) 1 ∨
      α = e8A2Beta ∨ α = e8A2NegBeta ∨ α = e8A2Delta ∨ α = e8A2Gamma} := by
  ext α
  constructor
  · intro hα
    simp only [e8A2Roots, Set.mem_setOf_eq] at hα
    rcases hα with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [e8A2Beta_lit] at h
      exact Or.inr (Or.inr (Or.inl h))
    · rw [e8A2NegBeta_lit] at h
      exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rw [e8A2Delta_lit] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rw [e8A2Gamma_lit] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rintro (h | h | h | h | h | h)
    · rw [h]
      exact Or.inl rfl
    · rw [h]
      exact Or.inr (Or.inl rfl)
    · rw [h, show e8A2Beta = (![0, 1, 1, 2, 2, 2, 1, 1] : Fin Tag.E8.rank → ℤ) from
        e8A2Beta_lit.symm]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h, show e8A2NegBeta = (-![0, 1, 1, 2, 2, 2, 1, 1] : Fin Tag.E8.rank → ℤ) from
        e8A2NegBeta_lit.symm]
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [h, show e8A2Delta = (![-1, -1, -1, -2, -2, -2, -1, -1] : Fin Tag.E8.rank → ℤ) from
        e8A2Delta_lit.symm]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rw [h, show e8A2Gamma = (-![-1, -1, -1, -2, -2, -2, -1, -1] : Fin Tag.E8.rank → ℤ) from
        e8A2Gamma_lit.symm]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem e8A2Roots_cases {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8A2Roots) :
    α = Pi.single (0 : Fin Tag.E8.rank) 1 ∨ α = -Pi.single (0 : Fin Tag.E8.rank) 1 ∨
      α = e8A2Beta ∨ α = e8A2NegBeta ∨ α = e8A2Delta ∨ α = e8A2Gamma := by
  rw [e8A2Roots_explicit] at hα
  exact hα

theorem e8A2RootsB_iff {α : Fin Tag.E8.rank → ℤ} :
    e8A2RootsB α = true ↔ α ∈ e8A2Roots := by
  rw [e8A2Roots_explicit]
  simp only [e8A2RootsB, Bool.or_eq_true, decide_eq_true_eq, Set.mem_setOf_eq]
  tauto

theorem isRoot_of_mem_e8A2Roots {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8A2Roots) :
    IsRoot Tag.E8 α := by
  simp only [e8A2Roots, Set.mem_setOf_eq] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact IsRoot.basis 0
  · exact IsRoot.neg (IsRoot.basis 0)
  · rw [show (![0, 1, 1, 2, 2, 2, 1, 1] : Fin Tag.E8.rank → ℤ) =
        toVec Tag.E8.rank [0, 1, 1, 2, 2, 2, 1, 1] by funext i; fin_cases i <;> rfl]
    exact isRoot_toVec (by decide +kernel)
  · rw [show (-![0, 1, 1, 2, 2, 2, 1, 1] : Fin Tag.E8.rank → ℤ) =
        -(toVec Tag.E8.rank [0, 1, 1, 2, 2, 2, 1, 1]) by
      funext i; fin_cases i <;> rfl]
    exact IsRoot.neg (isRoot_toVec (by decide +kernel))
  · rw [show (![-1, -1, -1, -2, -2, -2, -1, -1] : Fin Tag.E8.rank → ℤ) =
        -(toVec Tag.E8.rank [1, 1, 1, 2, 2, 2, 1, 1]) by
      funext i; fin_cases i <;> rfl]
    exact IsRoot.neg (isRoot_toVec (by decide +kernel))
  · rw [show (-![-1, -1, -1, -2, -2, -2, -1, -1] : Fin Tag.E8.rank → ℤ) =
        toVec Tag.E8.rank [1, 1, 1, 2, 2, 2, 1, 1] by
      funext i; fin_cases i <;> rfl]
    exact isRoot_toVec (by decide +kernel)

theorem e8A2Roots_subset_e8T3XKernel : e8A2Roots ⊆ e8T3XKernel := by
  intro α hα
  have hroot := isRoot_of_mem_e8A2Roots hα
  refine ⟨hroot, ?_, ?_⟩
  · simp only [e8A2Roots, Set.mem_setOf_eq] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [e8A2Roots, Set.mem_setOf_eq] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem e8A2Roots_subset_e8T3ZKernel : e8A2Roots ⊆ e8T3ZKernel := by
  intro α hα
  have hroot := isRoot_of_mem_e8A2Roots hα
  refine ⟨hroot, ?_, ?_⟩
  · simp only [e8A2Roots, Set.mem_setOf_eq] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [e8A2Roots, Set.mem_setOf_eq] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem neg_mem_e8A2Roots {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8A2Roots) :
    -α ∈ e8A2Roots := by
  rw [← e8A2RootsB_iff]
  rcases e8A2Roots_cases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem e8T3W_smul_mem_e8A2Roots :
    ∀ α ∈ e8A2Roots, e8T3W • α ∈ e8A2Roots := by
  intro α hα
  rw [← e8A2RootsB_iff]
  rcases e8A2Roots_cases hα with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [← weylMatrix_mulVec, weylMatrix_e8T3W]
    decide +kernel

theorem e8T3We_smul_mem_e8A2Roots {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∀ α ∈ e8A2Roots, e8T3We ε • α ∈ e8A2Roots := by
  rcases hε with rfl | rfl
  · intro α hα
    simpa only [e8T3We_one] using e8T3W_smul_mem_e8A2Roots α hα
  · intro α hα
    rw [e8T3We_smul (Or.inr rfl)]
    simp only [neg_one_smul]
    exact neg_mem_e8A2Roots (e8T3W_smul_mem_e8A2Roots α hα)


end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
