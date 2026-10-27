module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCo1
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRFi24
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRHN
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRHe
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRJ4Suz
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRLy
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRMathieu
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRMonster
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRONanOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRRuThCo2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRSmall
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

theorem twoNilpFor_isSporadic_holds (s : TauCeti.SporadicName) :
    TwoNilpFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y s := by
  cases s with
  | M11 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M11 SR.sporNoTwoFix_M11
  | M12 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M12 SR.sporNoTwoFix_M12
  | M22 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M22 SR.sporNoTwoFix_M22
  | M23 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M23 SR.sporNoTwoFix_M23
  | M24 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M24 SR.sporNoTwoFix_M24
  | J1 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.Foote5.sporadicOddCoreFree_J1 SR.sporNoTwoFix_J1
  | J2 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_J2 SR.sporNoTwoFix_J2
  | J3 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_J3 SR.sporNoTwoFix_J3
  | J4 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_J4 SR.sporNoTwoFix_J4
  | HS =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_HS SR.sporNoTwoFix_HS
  | McL =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_McL SR.sporNoTwoFix_McL
  | He => exact SR.twoNilpFor_He
  | Ru =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Ru SR.sporNoTwoFix_Ru
  | Suz =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Suz SR.sporNoTwoFix_Suz
  | ONan =>
    exact twoNilpFor_spor_of CFSG.Sporadic.ONOddCore.sporadicOddCoreFree_ONan SR.sporNoTwoFix_ONan
  | Co1 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Co1 SR.sporNoTwoFix_Co1
  | Co2 =>
    exact twoNilpFor_spor_of CFSG.Sporadic.Co2Schreier.sporadicOddCoreFree_Co2 SR.sporNoTwoFix_Co2
  | Co3 =>
    exact twoNilpFor_spor_of CFSG.Sporadic.SmallOddCore.sporadicOddCoreFree_Co3 SR.sporNoTwoFix_Co3
  | Fi22 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi22 SR.sporNoTwoFix_Fi22
  | Fi23 =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi23 SR.sporNoTwoFix_Fi23
  | Fi24Prime =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_Fi24Prime SR.sporNoTwoFix_Fi24
  | HN => exact twoNilpFor_spor_of CFSG.Sporadic.HNOddCore.sporadicOddCoreFree_HN SR.sporNoTwoFix_HN
  | Ly =>
    exact twoNilpFor_spor_of CFSG.Sporadic.LySchreier.sporadicOddCoreFree_Ly SR.sporNoTwoFix_Ly
  | Th =>
    exact twoNilpFor_spor_of CFSG.Sporadic.ThSchreier.sporadicOddCoreFree_Th SR.sporNoTwoFix_Th
  | B =>
    exact twoNilpFor_spor_of
      CFSG.ComponentClassification.BMCase.sporadicOddCoreFree_B SR.sporNoTwoFix_B
  | M => exact SR.twoNilpFor_M

end CFSG.ComponentClassification.HarrisLit.L33
