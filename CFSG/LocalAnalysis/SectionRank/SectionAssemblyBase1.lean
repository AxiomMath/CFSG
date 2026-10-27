
module

public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase

public import CFSG.LocalAnalysis.SectionRank.SimpleList
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData

@[expose] public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint

theorem catalogStepHyp_of_largeRee_J4
    (hree : LargeReeCatalogHyp) (hJ4 : J4OrderHyp) :
    CatalogStepHyp :=
  catalogStepHyp_of OddCover.catalogClassicalOddHyp EvenCover.catalog_classical_even
    (catalog_exceptional_even_of hree catalog_tits) (catalog_sporadic_of hJ4)

theorem sqt_catalog_of_simple_section_of_largeRee_J4
    (hree : LargeReeCatalogHyp)
    (hJ4 : J4OrderHyp) {X : Type} [Group X] [Finite X] (hX : IsSQTKCat X) (H : Subgroup X)
    (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)]
    (hnonab : ∃ a b : H ⧸ N, a * b ≠ b * a) :
    IsStronglyQuasithin (H ⧸ N) ∧ Catalog (H ⧸ N) :=
  sqt_catalog_of_simple_section oddKernelCentralization (catalogStepHyp_of_largeRee_J4 hree hJ4)
    hX H N hnonab

theorem catalogStepHyp_of_J4
    (hJ4 : J4OrderHyp) : CatalogStepHyp :=
  catalogStepHyp_of_largeRee_J4 LargeRee.catalog_large_ree hJ4

theorem sqt_catalog_of_simple_section_of_J4
    (hJ4 : J4OrderHyp) {X : Type} [Group X] [Finite X]
    (hX : IsSQTKCat X) (H : Subgroup X) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)]
    (hnonab : ∃ a b : H ⧸ N, a * b ≠ b * a) :
    IsStronglyQuasithin (H ⧸ N) ∧ Catalog (H ⧸ N) :=
  sqt_catalog_of_simple_section_of_largeRee_J4 LargeRee.catalog_large_ree hJ4 hX H N hnonab

end CFSG.SectionRank
