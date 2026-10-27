module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeTw
public import Certificates.Certificate17567
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeRk
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

set_option linter.unusedSectionVars false


namespace TabFi24

theorem shapeRkAt_fi24Rep3_three :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (fi24Rep3 3) := by
  obtain ⟨-, -, -, -, h4, -⟩ := fi24Three_facts
  exact Or.inl (pConstrainedShape_of_twinFacts h4 bound_base3 Certificates.certificate17567)

end TabFi24

end CFSG.HardMathSupport.Dickson.I271
