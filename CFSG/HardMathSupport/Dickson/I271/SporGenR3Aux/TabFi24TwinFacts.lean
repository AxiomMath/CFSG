module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Twin

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (jR cls)

open scoped commutatorElement

attribute [local instance] CFSG.Sporadic.Fi24.rAction


structure TwinFacts (w : List ℕ) : Prop where
  hK1 : ∀ a : Fin 306936, jR (wordElt w) • a = a →
    ∃ b : Fin 306936, TabFi23.Twin cls (jR (wordElt w)) a b
  hK2 : ∀ a b a' b' : Fin 306936, TabFi23.Twin cls (jR (wordElt w)) a b →
    TabFi23.Twin cls (jR (wordElt w)) a' b' → cls a' * cls b' = cls a * cls b →
    (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = cls a • b) ∨ (a' = cls a • b ∧ b' = a)
  hK3 : ∀ a₁ b₁ a₂ b₂ a₃ b₃ : Fin 306936, TabFi23.Twin cls (jR (wordElt w)) a₁ b₁ →
    TabFi23.Twin cls (jR (wordElt w)) a₂ b₂ → TabFi23.Twin cls (jR (wordElt w)) a₃ b₃ →
    ∀ f : Fin 306936, jR (wordElt w) • f = f →
    ⁅⁅cls a₁ * cls b₁, cls a₂ * cls b₂⁆, cls a₃ * cls b₃⁆ • f = f

end CFSG.HardMathSupport.Dickson.I271.TabFi24

end
