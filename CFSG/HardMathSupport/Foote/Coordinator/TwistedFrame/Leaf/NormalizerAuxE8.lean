module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxF4

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.E6 CFSG.RankThree.Lattice
open Matrix
open scoped MatrixGroups Matrix
open CFSG.RankThree.PartOne.KE (wordProd_smul_eq_wordMat_mulVec)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

set_option linter.unusedSectionVars false


theorem e8A4_isSLFrame (L : Type) [Field L] (v : WeylGroup Tag.E8) :
    IsSLFrame (rhoSigmaE8A4 L v) (sigmaRootE8A4 v) where
  isRoot i j hij := isRoot_sigmaRootE8A4 v hij
  neg i j := (sigmaRootE8A4_neg v i j).symm
  add i j k := sigmaRootE8A4_add v i j k
  transv i j hij := rhoSigmaE8A4_transvection v i j hij
  range := by
    rw [rhoSigmaE8A4_range, sigmaSetE8A4_eq]
    rfl

theorem S₂_e8Ten : TwClass.S₂ TwClass.e8Ten = {r | r ∈ e8ListA} := by
  ext α
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    have : ∀ m : Fin 240, (∀ i : Fin Tag.E8.rank, i.val ∉ ({0, 1, 2, 3} : Finset ℕ) →
        e8RootVec m i = 0) → e8RootVec m ∈ e8ListA := by decide +kernel
    exact this m hs
  · intro hr
    have : ∀ r ∈ e8ListA, (∃ m : Fin 240, e8RootVec m = r) ∧
        ∀ i : Fin Tag.E8.rank, i.val ∉ ({0, 1, 2, 3} : Finset ℕ) → r i = 0 := by decide +kernel
    obtain ⟨⟨m, rfl⟩, hs⟩ := this α hr
    exact ⟨isRoot_e8RootVec m, hs⟩


theorem S₁_e8Ten : TwClass.S₁ TwClass.e8Ten = {r | r ∈ e8ListB} := by
  ext β
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    rw [S₂_e8Ten] at ho
    have : ∀ m : Fin 240, (∀ α ∈ e8ListA, iform (τ := Tag.E8) (e8RootVec m) α = 0) →
        e8RootVec m ∈ e8ListB := by decide +kernel
    exact this m fun α hα => ho α hα
  · intro hr
    refine ⟨?_, fun α hα => ?_⟩
    · have : ∀ r ∈ e8ListB, ∃ m : Fin 240, e8RootVec m = r := by decide +kernel
      obtain ⟨m, rfl⟩ := this β hr
      exact isRoot_e8RootVec m
    · rw [S₂_e8Ten] at hα
      have : ∀ r ∈ e8ListB, ∀ α ∈ e8ListA, iform (τ := Tag.E8) r α = 0 := by decide +kernel
      exact this β hr α hα

theorem frameRoots_e8A : frameRoots (sigmaRootE8A4 e8VA) = {r | r ∈ e8ListA} := by
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    show sigmaRootE8A4 e8VA i j ∈ e8ListA
    rw [sigmaRootE8A4_eq_smul, e8VA_smul]
    exact e8A_img i j hij
  · intro hr
    obtain ⟨i, j, hij, h⟩ := e8A_cover r hr
    exact ⟨i, j, hij, by rw [sigmaRootE8A4_eq_smul, e8VA_smul]; exact h⟩

theorem frameRoots_e8B : frameRoots (sigmaRootE8A4 e8VB) = {r | r ∈ e8ListB} := by
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    show sigmaRootE8A4 e8VB i j ∈ e8ListB
    rw [sigmaRootE8A4_eq_smul, e8VB_smul]
    exact e8B_img i j hij
  · intro hr
    obtain ⟨i, j, hij, h⟩ := e8B_cover r hr
    exact ⟨i, j, hij, by rw [sigmaRootE8A4_eq_smul, e8VB_smul]; exact h⟩

theorem w_e8Ten_A : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

theorem w_e8Ten_B : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

theorem hπ_e8Ten_A (i j : Fin 5) (hij : i ≠ j) :
    (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • sigmaRootE8A4 e8VA i j =
      sigmaRootE8A4 e8VA (Fin.revPerm j) (Fin.revPerm i) := by
  have h1 : sigmaRootE8A4 e8VA i j = wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j :=
    (sigmaRootE8A4_eq_smul e8VA i j).trans (e8VA_smul _)
  have h2 : sigmaRootE8A4 e8VA (Fin.revPerm j) (Fin.revPerm i) =
      wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) :=
    (sigmaRootE8A4_eq_smul e8VA _ _).trans (e8VA_smul _)
  have h3 : (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • (wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j) :=
    wordProd_smul_eq_wordMat_mulVec Tag.E8 TwClass.wordE8Ten _
  exact (congrArg ((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • ·) h1).trans (h3.trans ((w_e8Ten_A i j hij).trans h2.symm))

theorem hπ_e8Ten_B (i j : Fin 5) (hij : i ≠ j) :
    (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • sigmaRootE8A4 e8VB i j =
      sigmaRootE8A4 e8VB (Fin.revPerm j) (Fin.revPerm i) := by
  have h1 : sigmaRootE8A4 e8VB i j = wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j :=
    (sigmaRootE8A4_eq_smul e8VB i j).trans (e8VB_smul _)
  have h2 : sigmaRootE8A4 e8VB (Fin.revPerm j) (Fin.revPerm i) =
      wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) :=
    (sigmaRootE8A4_eq_smul e8VB _ _).trans (e8VB_smul _)
  have h3 : (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • (wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j) :=
    wordProd_smul_eq_wordMat_mulVec Tag.E8 TwClass.wordE8Ten _
  exact (congrArg ((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • ·) h1).trans (h3.trans ((w_e8Ten_B i j hij).trans h2.symm))

theorem e8Ten_X₁ (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    CFSG.IsQuasisimple ↥(D.frame (TwClass.S₁ TwClass.e8Ten)) ∧
      Group.IsSolvable (Outer ↥(D.frame (TwClass.S₁ TwClass.e8Ten))) := by
  let r : Fin 5 → Fin 5 → Fin TwClass.e8Ten.tag.rank → ℤ := sigmaRootE8A4 e8VB
  have hfr : IsSLFrame (τ := TwClass.e8Ten.tag) (rhoSigmaE8A4 D.L e8VB) r :=
    e8A4_isSLFrame D.L e8VB
  have hinj := rhoSigmaE8A4_injective (L := D.L) e8VB
  have key := quasisimple_outer_solvable_fixedRoot_unitary D (ν := 5) (by norm_num)
    (fun h => absurd (congrArg Prod.fst h) (by simp)) hfr hinj Fin.revPerm
    (fun i j hij => hπ_e8Ten_B i j hij)
  have hS : frameRoots r = TwClass.S₁ TwClass.e8Ten := frameRoots_e8B.trans S₁_e8Ten.symm
  rw [hS] at key
  exact quasisimple_outer_frame_of_fixedRoot D key

theorem e8Ten_X₂ (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    CFSG.IsQuasisimple ↥(D.frame (TwClass.S₂ TwClass.e8Ten)) ∧
      Group.IsSolvable (Outer ↥(D.frame (TwClass.S₂ TwClass.e8Ten))) := by
  let r : Fin 5 → Fin 5 → Fin TwClass.e8Ten.tag.rank → ℤ := sigmaRootE8A4 e8VA
  have hfr : IsSLFrame (τ := TwClass.e8Ten.tag) (rhoSigmaE8A4 D.L e8VA) r :=
    e8A4_isSLFrame D.L e8VA
  have hinj := rhoSigmaE8A4_injective (L := D.L) e8VA
  have key := quasisimple_outer_solvable_fixedRoot_unitary D (ν := 5) (by norm_num)
    (fun h => absurd (congrArg Prod.fst h) (by simp)) hfr hinj Fin.revPerm
    (fun i j hij => hπ_e8Ten_A i j hij)
  have hS : frameRoots r = TwClass.S₂ TwClass.e8Ten := frameRoots_e8A.trans S₂_e8Ten.symm
  rw [hS] at key
  exact quasisimple_outer_frame_of_fixedRoot D key

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
