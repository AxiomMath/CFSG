module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Asc77

@[expose] def TwinSquareFact3 : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), e = 1 → StatedLieAdmissible t k 3 e →
    ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨ (t = .POmegaOdd ∧ k = 3) ∨
      (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) →
    ∀ R ∈ ModelFund 3 t k e, ∀ R' ∈ ModelFund 3 t k e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        x * x' ∈ Subgroup.center (modelUniv t k 3 e Fact.out).K →
        (∃ c ∈ Subgroup.center (modelUniv t k 3 e Fact.out).K, c * c = x * x') →
        t = .PSU ∧ k = 4

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
