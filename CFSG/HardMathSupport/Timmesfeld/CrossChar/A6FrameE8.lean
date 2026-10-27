module

public import CFSG.RankThree.PartOne.KE.E8A2Sigma
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6FrameCore

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

@[expose] def a6chainE8 : Fin 6 → Fin Tag.E8.rank :=
  ![e8Index 0, e8Index 2, e8Index 3, e8Index 4, e8Index 5, e8Index 6]

theorem exists_e8RootVec_a6 : ∀ a b : Fin 7, a ≠ b →
    ∃ m : Fin 240, e8RootVec m = chainRoot a6chainE8 a b := by
  decide +kernel

theorem a6ChainData_E8 :
    A6ChainData Tag.E8 a6chainE8 where
  simplyLaced := Or.inr (Or.inr (Or.inr rfl))
  isRoot a b hab := by
    obtain ⟨m, hm⟩ := exists_e8RootVec_a6 a b hab
    rw [← hm]
    exact isRoot_e8RootVec m
  add := by decide +kernel
  succ := by decide +kernel
  ne_pair := by decide +kernel
  orth := by decide +kernel

@[expose] def a6WordE8 : Fin 5 → List (Fin Tag.E8.rank)
  | 0 => []
  | 1 => [0, 2, 3]
  | 2 => [2, 3, 4, 0, 2, 3]
  | 3 => [3, 4, 5, 2, 3, 4, 0, 2, 3]
  | 4 => [4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3]

@[expose] def a6VE8 (c : Fin 5) : WeylGroup Tag.E8 :=
  (coxeterSystem Tag.E8).wordProd (a6WordE8 c)

theorem a6VE8_smul_zero : ∀ c : Fin 5,
    a6VE8 c • (Pi.single (e8Index 0) 1 : Fin Tag.E8.rank → ℤ) =
      Pi.single (a6chainE8 c.castSucc) 1 := by
  intro c
  rw [a6VE8, wordProd_smul_eq_wordMat_mulVec]
  revert c
  decide +kernel

theorem a6VE8_smul_two : ∀ c : Fin 5,
    a6VE8 c • (Pi.single (e8Index 2) 1 : Fin Tag.E8.rank → ℤ) =
      Pi.single (a6chainE8 c.succ) 1 := by
  intro c
  rw [a6VE8, wordProd_smul_eq_wordMat_mulVec]
  revert c
  decide +kernel

theorem a6ChainFrames_E8 : A6ChainFrames Tag.E8 a6chainE8 := by
  intro L _ c
  have h01 : sigmaRootE8 (a6VE8 c) 0 1 = Pi.single (a6chainE8 c.castSucc) 1 := by
    rw [sigmaRootE8_eq_smul, e8chainRoot13_values.1, a6VE8_smul_zero]
  have h12 : sigmaRootE8 (a6VE8 c) 1 2 = Pi.single (a6chainE8 c.succ) 1 := by
    rw [sigmaRootE8_eq_smul, e8chainRoot13_values.2.1, a6VE8_smul_two]
  have h10 : sigmaRootE8 (a6VE8 c) 1 0 = -Pi.single (a6chainE8 c.castSucc) 1 := by
    rw [← sigmaRootE8_neg, h01]
  have h21 : sigmaRootE8 (a6VE8 c) 2 1 = -Pi.single (a6chainE8 c.succ) 1 := by
    rw [← sigmaRootE8_neg, h12]
  refine exists_normalized_a2Frame_a6 (rhoSigmaE8 L (a6VE8 c)) _ _ ?_ ?_ ?_ ?_
  · obtain ⟨e, he⟩ := rhoSigmaE8_transvection (L := L) (a6VE8 c) 0 1 (by decide)
    exact ⟨e, fun t => by rw [he t, h01, pinnedX_single]⟩
  · obtain ⟨e, he⟩ := rhoSigmaE8_transvection (L := L) (a6VE8 c) 1 0 (by decide)
    exact ⟨e, fun t => by rw [he t, h10, pinnedX_neg_single]⟩
  · obtain ⟨e, he⟩ := rhoSigmaE8_transvection (L := L) (a6VE8 c) 1 2 (by decide)
    exact ⟨e, fun t => by rw [he t, h12, pinnedX_single]⟩
  · obtain ⟨e, he⟩ := rhoSigmaE8_transvection (L := L) (a6VE8 c) 2 1 (by decide)
    exact ⟨e, fun t => by rw [he t, h21, pinnedX_neg_single]⟩

variable (L : Type) [Field L]

variable {L}

theorem a6chainE8_cartan_one : ∀ t : Fin 6,
    Tag.E8.cartan (a6chainE8 t) (e8Index 1) = if t = 2 then -1 else 0 := by
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.CrossChar
