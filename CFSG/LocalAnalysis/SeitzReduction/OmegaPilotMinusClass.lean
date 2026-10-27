module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYModel
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus coordinateMinusWitnessEquiv regular_coordinateQuadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT matrix_simple_nonabelian)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed
  false_of_lieModel_omegaPlus_omegaMinus)

section Model

variable {K : Type} [Field K] [Finite K] {n f : ℕ}

theorem lieModel_coordinateMinus (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    LieModel (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) .POmegaMinus n 2
      f :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirr,
    ⟨(coordinateMinusWitnessEquiv _ (by omega) b c (MulEquiv.refl _)).symm⟩⟩

theorem isQuasisimple_coordinateMinus (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.IsQuasisimple (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  obtain ⟨hs, hnab⟩ := matrix_simple_nonabelian (by omega : 0 < 2 * n) hQ hT
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1

end Model

end CFSG.SeitzReduction.OmegaPilot
