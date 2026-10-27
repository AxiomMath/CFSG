module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Chart
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.OrthTrans
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenUnitary
public import CFSG.RankThree.PartOne.SEITZ3.NatArith

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup TauCeti CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg

section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def invCentGroup (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    Subgroup (twistedGroup σ) :=
  (slLong σ hσ).range ⊔ (CFSG.ClassicalInvolution.G2D4Models.slB σ hσ).range

end Defs

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
