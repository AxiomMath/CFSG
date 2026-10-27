module

public import CFSG.Assembly.SectionInduction
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface

public section

namespace CFSG.Assembly

theorem isKProperCat_of_kProper_inCatalog
    (hbridge : ∀ index, QuasithinUnique.B1.CatalogBridgeFor index)
    {G : Type} [Group G] [Finite G] (hK : KProper InCatalog G) : IsKProperCat G := by
  have hcatalog : KProper Blueprint.Catalog G :=
    KProper.of_catalogImp
      (fun sectionGroup _ _ _ _ hsection =>
        QuasithinUnique.B1.catalog_of_inCatalog hbridge sectionGroup hsection) hK
  exact KCore.KProperNonab.kProperAllSimple SectionRank.catalog_isoInvariant
    SectionRank.catalog_containsAbelianSimple hcatalog

end CFSG.Assembly
