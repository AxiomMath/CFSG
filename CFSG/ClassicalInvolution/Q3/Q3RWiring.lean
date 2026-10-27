module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired5
public import CFSG.ClassicalInvolution.Q3.Q3RCoreStep
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalInvolution.Asc77.TwinLookup
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.RankTwo
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8G2
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

theorem q3Inputs₅_of_residuals (hGH : GH74SectionalModels) (hQ : QuasisimpleConnected3)
    (hE : ClassicalMemberParametersE7TwE6) (hNL : SectionalFourNonLie3)
    (hlarge : CoreStep3Large) : Q3Inputs₅ :=
  ⟨hQ, coreStep3_of_gh74 hGH hE hNL hlarge, classicalIsFundamental3_proved⟩

end CFSG.ClassicalInvolution.MilestoneAssembly
