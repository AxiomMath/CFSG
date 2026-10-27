module

public import CFSG.RankThree.PartOne.KE.E7A2Sigma
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6FrameCore

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

@[expose] def a6chainE7 : Fin 6 → Fin Tag.E7.rank :=
  ![e7Index 0, e7Index 2, e7Index 3, e7Index 4, e7Index 5, e7Index 6]

theorem exists_e7RootVec_a6 : ∀ a b : Fin 7, a ≠ b →
    ∃ m : Fin 126, e7RootVec m = chainRoot a6chainE7 a b := by
  decide +kernel

theorem a6ChainData_E7 : A6ChainData Tag.E7 a6chainE7 where
  simplyLaced := Or.inr (Or.inr (Or.inl rfl))
  isRoot a b hab := by
    obtain ⟨m, hm⟩ := exists_e7RootVec_a6 a b hab
    rw [← hm]
    exact isRoot_e7RootVec m
  add := by decide +kernel
  succ := by decide +kernel
  ne_pair := by decide +kernel
  orth := by decide +kernel

@[expose] def a6WordE7 : Fin 5 → List (Fin Tag.E7.rank)
  | 0 => []
  | 1 => [0, 2, 3]
  | 2 => [2, 3, 4, 0, 2, 3]
  | 3 => [3, 4, 5, 2, 3, 4, 0, 2, 3]
  | 4 => [4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3]

@[expose] def a6VE7 (c : Fin 5) : WeylGroup Tag.E7 := (coxeterSystem Tag.E7).wordProd (a6WordE7 c)

theorem a6VE7_smul_zero : ∀ c : Fin 5,
    a6VE7 c • (Pi.single (e7Index 0) 1 : Fin Tag.E7.rank → ℤ) =
      Pi.single (a6chainE7 c.castSucc) 1 := by
  intro c
  rw [a6VE7, wordProd_smul_eq_wordMat_mulVec]
  revert c
  decide +kernel

theorem a6VE7_smul_two : ∀ c : Fin 5,
    a6VE7 c • (Pi.single (e7Index 2) 1 : Fin Tag.E7.rank → ℤ) =
      Pi.single (a6chainE7 c.succ) 1 := by
  intro c
  rw [a6VE7, wordProd_smul_eq_wordMat_mulVec]
  revert c
  decide +kernel

theorem a6ChainFrames_E7 : A6ChainFrames Tag.E7 a6chainE7 := by
  intro L _ c
  have h01 : sigmaRoot (a6VE7 c) 0 1 = Pi.single (a6chainE7 c.castSucc) 1 := by
    rw [sigmaRoot_eq_smul, chainRoot13_values.1, a6VE7_smul_zero]
  have h12 : sigmaRoot (a6VE7 c) 1 2 = Pi.single (a6chainE7 c.succ) 1 := by
    rw [sigmaRoot_eq_smul, chainRoot13_values.2.1, a6VE7_smul_two]
  have h10 : sigmaRoot (a6VE7 c) 1 0 = -Pi.single (a6chainE7 c.castSucc) 1 := by
    rw [← sigmaRoot_neg, h01]
  have h21 : sigmaRoot (a6VE7 c) 2 1 = -Pi.single (a6chainE7 c.succ) 1 := by
    rw [← sigmaRoot_neg, h12]
  refine exists_normalized_a2Frame_a6 (rhoSigma L (a6VE7 c)) _ _ ?_ ?_ ?_ ?_
  · obtain ⟨e, he⟩ := rhoSigma_transvection (L := L) (a6VE7 c) 0 1 (by decide)
    exact ⟨e, fun t => by rw [he t, h01, pinnedX_single]⟩
  · obtain ⟨e, he⟩ := rhoSigma_transvection (L := L) (a6VE7 c) 1 0 (by decide)
    exact ⟨e, fun t => by rw [he t, h10, pinnedX_neg_single]⟩
  · obtain ⟨e, he⟩ := rhoSigma_transvection (L := L) (a6VE7 c) 1 2 (by decide)
    exact ⟨e, fun t => by rw [he t, h12, pinnedX_single]⟩
  · obtain ⟨e, he⟩ := rhoSigma_transvection (L := L) (a6VE7 c) 2 1 (by decide)
    exact ⟨e, fun t => by rw [he t, h21, pinnedX_neg_single]⟩

variable (L : Type) [Field L]

variable {L}

theorem a6chainE7_cartan_one : ∀ t : Fin 6,
    Tag.E7.cartan (a6chainE7 t) (e7Index 1) = if t = 2 then -1 else 0 := by
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.CrossChar
