module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KThree
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem kProper_catalog_CBar {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (a : G) :
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog (CBar a) :=
  CFSG.KCore.KProperNonab.section CFSG.SectionRank.catalog_isoInvariant hK
    (centralizer ({a} : Set G)) (zpowersC a)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
