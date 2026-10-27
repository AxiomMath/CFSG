module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.Monster.SteinbergMSporadicOddCoreFree

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open CFSG.ComponentClassification CFSG.Blueprint

theorem sporadicOddCoreFree_of_ne_he
    (s : TauCeti.SporadicName) (hs : s ≠ .He) : CatalogueU.SporadicOddCoreFree s := by
  cases s with
  | M11 => exact CatalogueU.sporadicOddCoreFree_M11
  | M12 => exact CatalogueU.sporadicOddCoreFree_M12
  | M22 => exact CatalogueU.sporadicOddCoreFree_M22
  | M23 => exact CatalogueU.sporadicOddCoreFree_M23
  | M24 => exact CatalogueU.sporadicOddCoreFree_M24
  | J1 => exact Foote5.sporadicOddCoreFree_J1
  | J2 => exact CatalogueU.sporadicOddCoreFree_J2
  | J3 => exact CatalogueU.sporadicOddCoreFree_J3
  | J4 => exact CatalogueU.sporadicOddCoreFree_J4
  | Co1 => exact CatalogueU.sporadicOddCoreFree_Co1
  | Co2 => exact Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
  | Co3 => exact Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
  | Fi22 => exact CatalogueU.sporadicOddCoreFree_Fi22
  | Fi23 => exact CatalogueU.sporadicOddCoreFree_Fi23
  | Fi24Prime => exact CatalogueU.sporadicOddCoreFree_Fi24Prime
  | HS => exact CatalogueU.sporadicOddCoreFree_HS
  | McL => exact CatalogueU.sporadicOddCoreFree_McL
  | He => exact absurd rfl hs
  | Ru => exact CatalogueU.sporadicOddCoreFree_Ru
  | Suz => exact CatalogueU.sporadicOddCoreFree_Suz
  | ONan => exact Sporadic.ONOddCore.sporadicOddCoreFree_ONan
  | HN => exact Sporadic.HNOddCore.sporadicOddCoreFree_HN
  | Ly => exact Sporadic.LySchreier.sporadicOddCoreFree_Ly
  | Th => exact Sporadic.ThSchreier.sporadicOddCoreFree_Th
  | B => exact BMCase.sporadicOddCoreFree_B
  | M => exact CatalogueU.sporadicOddCoreFree_M

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
