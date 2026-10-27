module

public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogNativeLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogNativeBender
import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem qt_unique_model_outcomes_catalog {X : Type} [Group X]
    (h : fusionIsBenderGroup X ∨ UniqueSmallModel X) : CFSG.Blueprint.Catalog X := by
  rcases h with (⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩) |
    (⟨p, hp, hp7, -, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)
  · exact catalog_of_mulEquiv_psl_two_galoisField_two hf e
  · exact catalog_of_mulEquiv_psu3 hf e
  · exact catalog_of_mulEquiv_sz ha e
  · exact catalog_of_mulEquiv_psl_two_zmod hp hp7 e
  · exact catalog_of_mulEquiv_psl_three_zmod_three e
  · exact Or.inr
      (Or.inr
          (Or.inr
              (Or.inr
                  ⟨.M11,
                      ⟨(e.trans CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11.symm).trans
                          (MulEquiv.subgroupCongr
                              CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11)⟩⟩)))

theorem qt_unique_maximal_local_classification_cat_of_branches (hB : BenderBranch)
    (hC : ConstrainedBranch) (hU : UnconstrainedBranch)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : quasithinIsQTKECat G) (T : Sylow 2 G)
    (hT : ∃! M : Subgroup G,
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) :
    CFSG.Blueprint.Catalog G := by
  obtain ⟨M, h⟩ := uniqueSetting_of_sylow hnonab (qtkeCore_of_cat hnonab hqtke) T hT
  exact qt_unique_model_outcomes_catalog (theorem_2_1_1_of_branches hB hC hU h)

end CFSG.QuasithinUnique
