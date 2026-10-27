module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClHYc
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NoIrrFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.RestOrth
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusFinal
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusCent
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.FinalOfTypeBound
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1Frontier

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator


theorem sharedD2Inputs_of_open (hE6 : CoopersteinNoIrrFFE6) (hTE6 : CoopersteinNoIrrFFTwistedE6)
    (hLm : LieInput.OrthMinusLeviOb) (hCm : LieInput.OrthMinusCentOb)
    (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    CoopersteinNoFFExceptionalRestNoE8 ∧ StructureLie.EightNineNonParabolic ∧
      AlternatingGeometry.E0NonShortNotYStatement :=
  ⟨coopersteinNoFFExceptionalRestNoE8_of_e6Families hE6 hTE6,
    eightNineNonParabolic_of_lieInputRest
      (LieInput.lieInputRest_of_orth_nodes LieInput.orthPlusLeviOb LieInput.orthPlusCentOb hLm hCm),
    AlternatingGeometry.e0NonShortNotYStatement_of_hyp
      (AlternatingGeometry.e0NonShortNotHYpStatement_of_hyt
        (AlternatingGeometry.e0NonShortNotHYtStatement_of_hyz
          (AlternatingGeometry.e0NonShortNotHYzStatement_of_hyc hE0)))⟩

theorem sharedD2Inputs_of_rest (hTE6 : CoopersteinNoIrrFFTwistedE6)
    (hLm : LieInput.OrthMinusLeviOb) (hCm : LieInput.OrthMinusCentOb)
    (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    CoopersteinNoFFExceptionalRestNoE8 ∧ StructureLie.EightNineNonParabolic ∧
      AlternatingGeometry.E0NonShortNotYStatement :=
  sharedD2Inputs_of_open CurtisE6.coopersteinNoIrrFFE6 hTE6 hLm hCm hE0

theorem sharedD2Inputs_of_three
    (hT : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      TwE6.TwTypeBoundStmt hf K hK σ hσ)
    (hCm : LieInput.OrthMinusCentOb) (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    CoopersteinNoFFExceptionalRestNoE8 ∧ StructureLie.EightNineNonParabolic ∧
      AlternatingGeometry.E0NonShortNotYStatement :=
  sharedD2Inputs_of_rest (TwE6.coopersteinNoIrrFFTwistedE6_of_typeBound hT)
    LieInput.orthMinusLeviOb hCm hE0

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
