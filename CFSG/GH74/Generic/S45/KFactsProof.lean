module

public import CFSG.GH74.Generic.S45.Final
public import CFSG.GH74.Generic.S45.KBaseJ1
public import CFSG.GH74.Generic.S45.KBaseRee

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint CFSG.GH74.Generic

theorem reeTitsModel_of_lieModel {K : Type} [Group K] {f : ℕ}
    (h : LieModel K .twistedG2 0 3 f) : ReeTitsModel K .twistedG2 3 f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

theorem b_S45_KFacts :
    B_S45_KFacts := by
  intro K _ _ h
  rcases h with h | ⟨f, hf⟩
  · exact kBase_of_isSporadic_J1 h
  · exact kBase_of_reeModel (reeTitsModel_of_lieModel hf)

theorem s_shapeCase_S4_of_pumpup
    (hP : B_S45_pumpup) : S_shapeCaseMaxNT @ShapeS4 :=
  s_shapeCase_S4_of_leaves b_S45_KFacts hP

theorem s_shapeCase_S5_of_pumpup
    (hP : B_S45_pumpup) : S_shapeCaseMaxNT @ShapeS5 :=
  s_shapeCase_S5_of_leaves b_S45_KFacts hP

end CFSG.GH74.Generic.S45
