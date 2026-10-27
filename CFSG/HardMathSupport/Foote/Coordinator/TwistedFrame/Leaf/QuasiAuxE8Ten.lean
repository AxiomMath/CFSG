module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxUnitary
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 CFSG.RankThree.Lattice
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open scoped MatrixGroups

set_option linter.unusedSectionVars false


namespace QuasiE8Ten

@[expose] def wE8Ten : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten

theorem w_smul (x : Fin Tag.E8.rank → ℤ) :
    (wE8Ten • x : Fin Tag.E8.rank → ℤ) = wordMat Tag.E8 TwClass.wordE8Ten *ᵥ x :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 TwClass.wordE8Ten x

theorem S₂_sub : ∀ β ∈ rootFinset Tag.E8,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → β i = 0) → β ∈ e8ListA := by
  decide +kernel

theorem A_root : ∀ β ∈ e8ListA, β ∈ rootFinset Tag.E8 ∧
    ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → β i = 0 := by decide +kernel

theorem S₂_eq : TwClass.e8Ten.S₂ = {r | r ∈ e8ListA} := by
  ext β
  show (IsRoot Tag.E8 β ∧ ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → β i = 0) ↔
    β ∈ e8ListA
  constructor
  · rintro ⟨hβ, hs⟩
    exact S₂_sub β (mem_rootFinset.2 hβ) hs
  · intro hβ
    exact ⟨mem_rootFinset.1 (A_root β hβ).1, (A_root β hβ).2⟩

theorem S₁_sub : ∀ β ∈ rootFinset Tag.E8, (∀ α ∈ e8ListA, iform (τ := Tag.E8) β α = 0) →
    β ∈ e8ListB := by decide +kernel

theorem B_root : ∀ β ∈ e8ListB, β ∈ rootFinset Tag.E8 ∧
    ∀ α ∈ e8ListA, iform (τ := Tag.E8) β α = 0 := by decide +kernel

theorem S₁_eq : TwClass.e8Ten.S₁ = {r | r ∈ e8ListB} := by
  ext β
  show (IsRoot Tag.E8 β ∧ ∀ α ∈ TwClass.e8Ten.S₂, iform (τ := Tag.E8) β α = 0) ↔ β ∈ e8ListB
  constructor
  · rintro ⟨hβ, hs⟩
    exact S₁_sub β (mem_rootFinset.2 hβ) fun α hα => by
      rw [S₂_eq] at hs
      exact hs α hα
  · intro hβ
    refine ⟨mem_rootFinset.1 (B_root β hβ).1, fun α hα => ?_⟩
    rw [S₂_eq] at hα
    exact (B_root β hβ).2 α hα

theorem sigmaSet_A : sigmaSetE8A4 e8VA = {r | r ∈ e8ListA} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_setOf_eq, sigmaRootE8A4_eq_smul, e8VA_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8A_img i j hij
  · intro hr
    exact e8A_cover r hr

theorem sigmaSet_B : sigmaSetE8A4 e8VB = {r | r ∈ e8ListB} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_setOf_eq, sigmaRootE8A4_eq_smul, e8VB_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8B_img i j hij
  · intro hr
    exact e8B_cover r hr

theorem graph_A : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

theorem graph_B : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

end QuasiE8Ten

theorem isQuasisimple_e8Ten_X₂ {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    CFSG.IsQuasisimple ↥(TwClass.e8Ten.X₂ D) := by
  refine D.isQuasisimple_frame ?_
  choose! ε hε using fun i j hij => rhoSigmaE8A4_transvection (L := D.L) e8VA i j hij
  refine D.isQuasisimple_fixedRoot_unitary (ν := 5) (by norm_num) (Or.inl (by norm_num))
    (S := TwClass.e8Ten.S₂) (fun r hr => hr.1) (rhoSigmaE8A4 D.L e8VA)
    (rhoSigmaE8A4_injective e8VA) ?_
    (fun b => ⟨fun i => rootChar b (wbE8A4 e8VA i), fun A => rhoSigmaE8A4_torus e8VA b A⟩)
    (fun A hA => rhoSigmaE8A4_diagonal e8VA A hA) (sigmaRootE8A4 e8VA)
    (fun i j hij => isRoot_sigmaRootE8A4 e8VA hij) ε (fun i j hij t => hε i j hij t)
    Fin.revPerm ?_
  · exact (rhoSigmaE8A4_range e8VA).trans (congrArg (rootSpan Tag.E8 D.L)
      (QuasiE8Ten.sigmaSet_A.trans QuasiE8Ten.S₂_eq.symm))
  · intro i j hij
    show (QuasiE8Ten.wE8Ten • sigmaRootE8A4 e8VA i j : Fin Tag.E8.rank → ℤ) =
      sigmaRootE8A4 e8VA (Fin.revPerm j) (Fin.revPerm i)
    rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, QuasiE8Ten.w_smul, e8VA_smul, e8VA_smul]
    exact QuasiE8Ten.graph_A i j hij

theorem isQuasisimple_e8Ten_X₁ {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    CFSG.IsQuasisimple ↥(TwClass.e8Ten.X₁ D) := by
  refine D.isQuasisimple_frame ?_
  choose! ε hε using fun i j hij => rhoSigmaE8A4_transvection (L := D.L) e8VB i j hij
  refine D.isQuasisimple_fixedRoot_unitary (ν := 5) (by norm_num) (Or.inl (by norm_num))
    (S := TwClass.e8Ten.S₁) (fun r hr => hr.1) (rhoSigmaE8A4 D.L e8VB)
    (rhoSigmaE8A4_injective e8VB) ?_
    (fun b => ⟨fun i => rootChar b (wbE8A4 e8VB i), fun A => rhoSigmaE8A4_torus e8VB b A⟩)
    (fun A hA => rhoSigmaE8A4_diagonal e8VB A hA) (sigmaRootE8A4 e8VB)
    (fun i j hij => isRoot_sigmaRootE8A4 e8VB hij) ε (fun i j hij t => hε i j hij t)
    Fin.revPerm ?_
  · exact (rhoSigmaE8A4_range e8VB).trans (congrArg (rootSpan Tag.E8 D.L)
      (QuasiE8Ten.sigmaSet_B.trans QuasiE8Ten.S₁_eq.symm))
  · intro i j hij
    show (QuasiE8Ten.wE8Ten • sigmaRootE8A4 e8VB i j : Fin Tag.E8.rank → ℤ) =
      sigmaRootE8A4 e8VB (Fin.revPerm j) (Fin.revPerm i)
    rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, QuasiE8Ten.w_smul, e8VB_smul, e8VB_smul]
    exact QuasiE8Ten.graph_B i j hij

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
