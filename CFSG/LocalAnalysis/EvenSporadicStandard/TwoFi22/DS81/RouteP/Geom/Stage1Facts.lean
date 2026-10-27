module

public import Certificates.Certificate450240

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three


theorem stage1_stab_transitive {c : Ω} (h0 : Δ.Adj x0 c) (h1 : Δ.Adj x1 c) (h2 : Δ.Adj x2 c) :
    ∃ h ∈ A1gen, h • x2 = x2 ∧ h • planePt 3 = c :=
  Certificates.certificate450240.stab_transitive h0 h1 h2

theorem stage1_sem : ∃ y w : Ω, Stage1Sem y w := Certificates.certificate450240

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

end
