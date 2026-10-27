module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Assembly
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4ClassReduce
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4ClassTwo
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4ClassLarge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin

theorem ffOffenderInvertsOddD4_holds :
    FFOffenderInvertsOddD4 :=
  ffOffenderInvertsOddD4_of_natural_classification
    (FFO.D4.natural_classification_of_leaves
      (fun _ _ _ _ hK _ _ _ hV L E θ hirr hEN hE hEel hEq hoff =>
        FFO.D4.exists_natural_of_quadratic_offender_card_two hK hV L E θ hirr hEN hE hEel hEq hoff)
      (fun _ _ _ _ hK _ _ _ hV L E θ hirr hEN hE hEel hEq hoff =>
        FFO.D4.exists_natural_of_quadratic_offender_four_le hK hV L E θ hirr hEN hE hEel hEq hoff))

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
