module

public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeBender
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeM11
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem inCatalog_of_fusionIsBenderGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (h : fusionIsBenderGroup X) :
    CFSG.Assembly.InCatalog X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact inCatalog_of_mulEquiv_psl_two_galoisField_two hf e
  · exact inCatalog_of_mulEquiv_psu3 hnonab hf e
  · exact inCatalog_of_mulEquiv_sz ha e

theorem inCatalog_of_uniqueSmallModel
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (h : UniqueSmallModel X) :
    CFSG.Assembly.InCatalog X := by
  have _ := hnonab
  rcases h with ⟨p, hp, hp7, -, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact inCatalog_of_mulEquiv_psl_two_zmod hp hp7 e
  · exact inCatalog_of_mulEquiv_psl_three_zmod_three e
  · exact inCatalog_of_mulEquiv_m11 e

theorem qt_unique_maximal_local_classification_of_branches
    (hTC : TCKGroupBridgeSQT)
    (hB : BenderBranch) (hC : ConstrainedBranch) (hU : UnconstrainedBranch)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.Assembly.Quasithin.quasithinIsQTKE G) (T : Sylow 2 G)
    (hT : ∃! M : Subgroup G,
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) :
    CFSG.Assembly.InCatalog G := by
  obtain ⟨M, h⟩ := uniqueSetting_of_sylow hnonab (qtkeCore_of_tauCeti hTC hnonab hqtke) T hT
  rcases theorem_2_1_1_of_branches hB hC hU h with hb | hs
  · exact inCatalog_of_fusionIsBenderGroup hnonab hb
  · exact inCatalog_of_uniqueSmallModel hnonab hs

end CFSG.QuasithinUnique
