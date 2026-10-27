module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.RootData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
open scoped Matrix


@[expose] def wF : WeylGroup Tag.F4 := TwClass.f4Six.w

@[expose] def r3 : Fin Tag.F4.rank → ℤ := Pi.single 2 1
@[expose] def r4 : Fin Tag.F4.rank → ℤ := Pi.single 3 1

theorem wF_smul (α : Fin Tag.F4.rank → ℤ) : wF • α = wordMat Tag.F4 TwClass.wordF4 *ᵥ α :=
  wordProd_smul_eq_wordMat_mulVec Tag.F4 TwClass.wordF4 α

theorem wF_r3 : wF • r3 = r4 := by
  rw [wF_smul]; unfold r3 r4; decide +kernel

theorem wF_r4 : wF • r4 = r3 := by
  rw [wF_smul]; unfold r3 r4; decide +kernel

theorem wF_r34 : wF • (r3 + r4) = r3 + r4 := by
  rw [wF_smul]; unfold r3 r4; decide +kernel

theorem wF_alpha1 : wF • DetectF4.alpha1 = DetectF4.root1342 := by
  rw [wF_smul]; decide +kernel

theorem wF_root1342 : wF • DetectF4.root1342 = DetectF4.alpha1 := by
  rw [wF_smul]; decide +kernel

theorem wF_theta : wF • highRoot Tag.F4 = highRoot Tag.F4 := by
  rw [wF_smul]; decide +kernel

theorem wF_invol (α : Fin Tag.F4.rank → ℤ) : wF • (wF • α) = α := by
  rw [wF_smul, wF_smul, Matrix.mulVec_mulVec]
  have : wordMat Tag.F4 TwClass.wordF4 * wordMat Tag.F4 TwClass.wordF4 = 1 := by decide +kernel
  rw [this, Matrix.one_mulVec]

theorem wF_deg : ∀ α ∈ rootFinset Tag.F4, (wF • α) 0 = α 0 := by
  intro α hα
  rw [wF_smul]
  revert α
  decide +kernel

theorem wF_mRoots : ∀ ν ∈ mRoots, wF • ν ∈ mRoots ∧ (wF • ν) 1 ≠ ν 1 := by
  intro ν hν
  rw [wF_smul]
  revert ν
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
