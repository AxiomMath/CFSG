module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelSelfDual
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelPaired

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem orthComponentBlockAnalysis_of_blocks {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hQne : ∃ v, Q v ≠ 0)
    (hpair : OrthPairedBlock Q) (hself : OrthSelfDualBlock Q) :
    OrthComponentBlockAnalysis Q :=
  orthComponentBlockAnalysis_of_cases hQ hQne hpair hself (orthFixedBlock_holds Q)

theorem orthComponentBlockAnalysis_holds_of_residuals
    (hpair : OrthPairedBlockModelResidual) (hself : OrthSelfDualCatalogue) :
    ∀ {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate → (∃ v, Q v ≠ 0) →
      OrthComponentBlockAnalysis Q := by
  intro K V _ _ _ _ _ _ Q hQ hQne
  exact orthComponentBlockAnalysis_of_blocks hQ hQne
    (orthPairedBlock_holds_of_model_residual hpair Q)
    (orthSelfDualBlock_of_catalogue hself (Q := Q))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end