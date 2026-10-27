module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwAnyKind

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem noFrobeniusInnerAny_of_outer (τ : Tag) : NoFrobeniusInnerAny τ := by
  intro L _ _ p S hτ hq4 D₁ hD₁E h
  exact noFrobeniusInner_of_big_any S hτ hq4 hD₁E h

theorem anyKindNoFrobenius_of_outer : AnyKindNoFrobenius := by
  intro τ L _ _ p S hτ hq4 D₁ hD₁E h
  exact noFrobeniusInner_of_big_any S hτ hq4 hD₁E h

end CFSG.HardMathSupport.Timmesfeld.LangTorus
