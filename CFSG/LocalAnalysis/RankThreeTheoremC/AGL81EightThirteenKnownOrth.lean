module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownOrthSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownOrthPlus
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownOrthMinus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem threeCoreAt_Sp82 : ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSp 4 (GaloisField 2 1)) :=
  threeCoreAt_of_threePlaneGen CFSG.RankThree.PartTwo.Sec4.RonanK432.sp82Equiv.symm
    OrthPlanes.threePlaneGen_H8

theorem threeCoreAt_O8p :
    ThreeCoreAt (CFSG.Assembly.RankThreeEven.projOmegaPlus 4 (GaloisField 2 1)) :=
  threeCoreAt_of_threePlaneGen CFSG.RankThree.PartTwo.Sec4.RonanK429E.O8.projEquiv.symm
    OrthPlanes.threePlaneGen_OM

theorem threeCoreAt_O8m {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    ThreeCoreAt (CFSG.Assembly.RankThreeEven.projOmegaMinus 3 (GaloisField 2 1) b c) :=
  threeCoreAt_of_threePlaneGen
    (CFSG.RankThree.PartTwo.Sec4.RonanK429F.nonempty_projOmegaMinus_equiv_om8 hbc).some.symm
    OrthPlanes.threePlaneGen_Om8

end CFSG.LocalAnalysis.RankThreeTheoremC
