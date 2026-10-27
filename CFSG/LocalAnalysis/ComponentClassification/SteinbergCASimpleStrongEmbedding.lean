module

public import CFSG.Milestones.SE_simple_strong_embedding_models
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogNativeBender
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogNativeLinear
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.ComponentClassification.SteinbergCA

theorem catalog_of_isBenderGroup {X : Type} [Group X] (h : CFSG.BenderSuzuki.IsBenderGroup X) :
    CFSG.Blueprint.Catalog X := by
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact CFSG.QuasithinUnique.catalog_of_mulEquiv_psl_two_galoisField_two hn e
  · exact CFSG.QuasithinUnique.catalog_of_mulEquiv_sz hn
      (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz n)))
  · have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
        CFSG.Models.benderPSU3Model_eq_psu3 n
    exact CFSG.QuasithinUnique.catalog_of_mulEquiv_psu3 hn
      (e.trans (MulEquiv.subgroupCongr hmodel))

theorem simple_strong_embedding_catalog (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hse : ∃ M : Subgroup G, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    CFSG.Blueprint.Catalog G := by
  have _ := hnonab
  obtain ⟨M, hM⟩ := hse
  exact catalog_of_isBenderGroup (CFSG.Milestones.bender_suzuki M hM)

end CFSG.ComponentClassification.SteinbergCA
