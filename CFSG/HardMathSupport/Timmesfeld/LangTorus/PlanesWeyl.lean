module

public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false

theorem toMat_e7TwoMat : toMat Tag.E7.rank e7TwoMat = -1 := by decide +kernel

theorem toMat_e8TwoMat : toMat Tag.E8.rank e8TwoMat = -1 := by decide +kernel

theorem exists_weyl_neg_E7 : ∃ w : WeylGroup Tag.E7, ∀ u : Fin Tag.E7.rank → ℤ, w • u = -u := by
  obtain ⟨w, hw⟩ := IsWeylMatrix.of_word Tag.E7 e7TwoWord
  exact ⟨w, fun u => by rw [hw, e7Two_wordMat, toMat_e7TwoMat, Matrix.neg_mulVec,
    Matrix.one_mulVec]⟩

theorem exists_weyl_neg_E8 : ∃ w : WeylGroup Tag.E8, ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u := by
  obtain ⟨w, hw⟩ := IsWeylMatrix.of_word Tag.E8 e8TwoWord
  exact ⟨w, fun u => by rw [hw, e8Two_wordMat, toMat_e8TwoMat, Matrix.neg_mulVec,
    Matrix.one_mulVec]⟩

end CFSG.HardMathSupport.Timmesfeld.LangTorus
