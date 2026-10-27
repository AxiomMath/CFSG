module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairE6
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairF4
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Perfect
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Swap
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

theorem excPairCent
    : ExcPairCent := by
  intro S _ _ h x y hx hy hxy hne
  rcases h with h | h
  · exact PairF4.not_pairCent_F4 h hx hy hxy hne
  · exact fun hc => PairE6.not_pairCent_twistedE6 h hx hy hne hc.1

end CFSG.ComponentClassification.RankTwoExceptional
