module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5All
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Sec44
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Top
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec3In

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three

section Certified


theorem yamadaCase3Core_wire (hF : G23Facts) (h62' : Sec62') (h63' : Sec63') (h64b' : Sec64b')
    (hA : Sec7A) (hB' : Sec7B) (hC : Sec7C) (hNT : Sec7NT) (h1R : Gomi1RKP) :
    YamadaCase3Core := by
  have hB : Sec3Inputs := sec3Inputs_of
  have h5 : Sec5 := sec5_of_sec3Inputs hB
  have h61' : Sec61' := sec61'_of hB
  have h6 : Sec6 := sec6_of_primed h5 h61' h62' h63'
  exact yamadaCase3Core_of_basic_inputs_kp hF (sec42_of hB) (sec44_of hB) (sec52_of hB)
    (sec53_of hB) (sec54_of hB) (sec55_of hB) (sec56_of hB) (sec57_of hB) (sec61_of h5 h61')
    (sec62_of h5 h62') (sec63_of h5 h61' h62' h63') (sec64a_of h5 h6 (sec64a'_of hB))
    (sec64b_of h5 h6 h64b') (sec7False_of hB (sec7_of_stages hA hB' hC) hNT) h1R

end Certified

end CFSG.OddStandard.HigherRank.YamadaG23
