module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClInner
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem innDiagOn_of_innerOn_setup
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (hS : Setup p L J A d b) (h : InnerOn J b) :
    InnDiagOn p (Subgroup.zpowers b) J :=
  innDiagOn_of_innerOn hS.prime hS.pcomp hS.chevJ hS.b_norm h

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
