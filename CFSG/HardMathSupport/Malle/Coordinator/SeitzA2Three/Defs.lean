module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def heisCube {F : Type} [Field F] (σ : F ≃+* F) (lam ω : Fˣ) :
    Subgroup (MulAut (projectiveSL 3 F)) :=
  Subgroup.zpowers (fieldAut 3 F σ) ⊔
    (Subgroup.zpowers (conjAut 3 F
        (CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL F 1 ω (ω ^ 2))) ⊔
      Subgroup.zpowers (conjAut 3 F
        (CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.monomGL F lam)))

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
