module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafU4Char2
public import CFSG.Adapters.ClassicalCatalogReverse

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open CFSG.Quasithin

theorem for_PSp43
    (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => StatedClassicalModel S .PSp 2 3 1) :=
  For.mono (fun _ _ h => ⟨1, le_rfl,
      CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three h⟩)
    (for_U4char2 h37 h38 h39)

end CFSG.SectionRank.QTK.Insp443

end
