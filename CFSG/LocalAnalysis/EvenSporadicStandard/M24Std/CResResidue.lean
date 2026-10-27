module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2A8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2L52
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Sp44
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ResidueDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank

theorem residue_cA8 :
    Ega81Sit fun _ _ _ _ _ _ _ C _ =>
      Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃* alternatingGroup (Fin 8)) →
        False := by
  intro G _ _ L z _ _ hs A B C D hF he
  exact false_of_layer_eData hs hF (eData_A8 he)

theorem residue_cU42 :
    Ega81Sit fun _ _ _ _ _ _ _ C _ =>
      LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSU 4 2 1 → False := by
  intro G _ _ L z _ _ hs A B C D hF he
  exact false_of_layer_eData hs hF (eData_U42 he)

theorem residue_cL52 :
    Ega81Sit fun _ _ _ _ _ _ _ C _ =>
      LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSL 5 2 1 → False := by
  intro G _ _ L z _ _ hs A B C D hF he
  exact false_of_layer_eData hs hF (eData_L52 he)

theorem residue_cU52 :
    Ega81Sit fun _ _ _ _ _ _ _ C _ =>
      LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSU 5 2 1 → False := by
  intro G _ _ L z _ _ hs A B C D hF he
  exact false_of_layer_eData hs hF (eData_U52 he)

theorem residue_cSp44 :
    Ega81Sit fun _ _ _ _ _ _ _ C _ =>
      LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSp 2 2 2 → False := by
  intro G _ _ L z _ _ hs A B C D hF he
  exact false_of_layer_eData hs hF (eData_Sp44 he)

end CFSG.EvenSporadicStandard.M24Std
