module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramE7
public import CFSG.LieType.Chevalley.RationalToralSignDiagramE6
public import CFSG.LieType.Chevalley.RationalToralSignDiagramD4

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley ToralSign

theorem rational_toral_sign_diagram_arithmetic :
    RationalToralSignDiagram .E7 (1 : Equiv.Perm (Fin Tag.E7.rank)) 2 e7SignDiagramReps ∧
      RationalToralSignDiagram .E6 (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank)) 2
        e6SignDiagramReps ∧
      RationalToralSignDiagram .D4 (TwistTag.D4.perm : Equiv.Perm (Fin Tag.D4.rank)) 3
        d4SignDiagramReps :=
  ⟨rationalToralSignDiagram_E7, rationalToralSignDiagram_E6, rationalToralSignDiagram_D4⟩

end CFSG.LieType.Chevalley
