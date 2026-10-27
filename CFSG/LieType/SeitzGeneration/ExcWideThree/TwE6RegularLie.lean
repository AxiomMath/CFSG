module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieCore
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularSA

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

section Lie


theorem twE6InnerLineLie_holds : TwE6InnerLineLie := by
  intro K _ _ σ q hK3 hσ hK E hE D e heE _ a ha β₁ β₂ hβ₁ hβ₂ hβ₁₂ hχ₁ hχ₂ hv₁ hv₂
  exact twE6InnerLineLie_core K σ q hK3 hσ hK E hE D e heE a ha β₁ β₂ hβ₁ hβ₂ hβ₁₂ hχ₁ hχ₂
    hv₁ hv₂

end Lie

end CFSG.LieType.SeitzGeneration.ExcWideThree
