module

public import CFSG.GH74.GLS.Stage2.Local.GHSchLie
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public import CFSG.Sporadic.Schreier.PairMcLPairs
public import CFSG.Sporadic.Schreier.LySchreierCase

public section

namespace CFSG.GH74.GLS.Stage2.Local.GHSch

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.SporadicSchreierDispatch

theorem ghSporadicCases
    : GHSporadicCases where
  M11 := sporadicSchreierCase_M11
  M12 := sporadicSchreierCase_M12
  M22 := sporadicSchreierCase_M22
  M23 := sporadicSchreierCase_M23
  J1 := sporadicSchreierCase_J1
  J2 := sporadicSchreierCase_of_outer CFSG.Sporadic.Schreier.AT_J2_Schreier.2.2
  J3 := sporadicSchreierCase_of_outer CFSG.Sporadic.Schreier.AT_J3_Schreier.2
  McL := sporadicSchreierCase_of_outer CFSG.Sporadic.Schreier.AT_McL_Schreier.2
  Ly := CFSG.Sporadic.LySchreier.sporadicSchreierCase_Ly

theorem ghSchreier_thm
    : SchreierFor GHList :=
  ghSchreier_of_sporadic ghSporadicCases

end CFSG.GH74.GLS.Stage2.Local.GHSch
