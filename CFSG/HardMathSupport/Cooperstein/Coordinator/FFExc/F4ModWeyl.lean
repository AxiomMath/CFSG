module

public import CFSG.LieType.SeitzGeneration.ExcTorusF4Two

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice


theorem exists_weyl_neg_F4' :
    ∃ w0 : WeylGroup Tag.F4, ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u := by
  refine ⟨(coxeterSystem Tag.F4).wordProd f4TwoWord, fun u => ?_⟩
  have h : toMat Tag.F4.rank f4TwoMat = (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) := by
    decide +kernel
  rw [wordProd_smul_eq_wordMat_mulVec, f4Two_wordMat, h, Matrix.neg_mulVec, Matrix.one_mulVec]

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
