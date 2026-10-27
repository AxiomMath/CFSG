module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.HardMathSupport.Dickson.Sec6

theorem u42Outer_holds :
    U42Outer := by
  refine u42Outer_of_cover (F := fun d => FamA1 d ∨ FamA2 d ∨ FamAHigh d ∨ FamTwA2 d ∨
    FamTwAHigh d ∨ FamB d ∨ FamD4 d ∨ FamDHigh d ∨ FamTwD d ∨ FamE6 d ∨ FamTwE6 d ∨ FamE7 d ∨
    FamE8 d ∨ FamF4 d ∨ FamG2 d ∨ FamTriD4 d ∨ FamSz d ∨ FamReeF4 d ∨ FamTits d)
    (fun d hc => famCover d hc) ?_
  refine u42Out_A1.union ?_
  refine u42Out_A2.union ?_
  refine u42Out_AHigh.union ?_
  refine u42Out_twA2.union ?_
  refine u42Out_twAHigh.union ?_
  refine u42Out_B.union ?_
  refine u42Out_d4.union ?_
  refine u42Out_dHigh.union ?_
  refine u42Out_twD.union ?_
  refine u42Out_e6.union ?_
  refine u42Out_twE6.union ?_
  refine u42Out_e7.union ?_
  refine u42Out_e8.union ?_
  refine u42Out_f4.union ?_
  refine u42Out_g2.union ?_
  refine u42Out_triD4.union ?_
  refine u42Out_sz.union ?_
  exact u42Out_reeF4.union u42Out_tits

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
