module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionM

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

theorem leafB27Contradiction [G23Leaf LeafGL3Facts] : LeafB27Contradiction := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm W₁ Mf t' h hF hO hL hPb ha₁ ha₂ hst
  exact main_contradiction h hF hO hL hPb ha₁ ha₂ hst

end CFSG.GH74.QTGen4.Recog.G23.P7

end
