module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Burnside
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

@[expose] def LieFamilyA : TauCeti.LieTypeIndex → Prop
  | .A _ _ => True
  | .twistedA _ _ => True
  | _ => False

@[expose] def LieFamilyClassical : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | .C _ _ => True
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

@[expose] def LieFamilyExceptional : TauCeti.LieTypeIndex → Prop
  | .E6 _ => True
  | .E7 _ => True
  | .E8 _ => True
  | .F4 _ => True
  | .G2 _ => True
  | .twistedE6 _ => True
  | .trialityD4 _ => True
  | _ => False

@[expose] def LieFamilyHalf : TauCeti.LieTypeIndex → Prop
  | .suzuki _ => True
  | .reeG2 _ => True
  | .reeF4 _ => True
  | .tits => True
  | _ => False

theorem lieFamily_cases (i : TauCeti.LieTypeIndex) :
    LieFamilyA i ∨ LieFamilyClassical i ∨ LieFamilyExceptional i ∨ LieFamilyHalf i := by
  cases i <;> simp [LieFamilyA, LieFamilyClassical, LieFamilyExceptional, LieFamilyHalf]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
