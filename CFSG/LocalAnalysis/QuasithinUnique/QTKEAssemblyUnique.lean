module

public import CFSG.LocalAnalysis.QuasithinUnique.QTKEAssembly
public import CFSG.Milestones.QT_unique_maximal_local_classification

public section

namespace CFSG.QuasithinUnique

theorem uniqueMaximalLocalCat_proved
    : UniqueMaximalLocalCat :=
  fun G _ _ _ hnonab hqtke T hT =>
    CFSG.Milestones.qt_unique_maximal_local_classification G hnonab hqtke T hT

theorem cls_qtke_classification_of_D_E
    (hE : FaithfulLocalEmptyCat) (hD : FaithfulLocalNonemptyCat) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : quasithinIsQTKECat G) :
    Blueprint.Catalog G :=
  cls_qtke_classification_of_branches uniqueMaximalLocalCat_proved hE hD G hnonab hqtke

end CFSG.QuasithinUnique
