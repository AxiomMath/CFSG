module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YMain
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Intro
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y51
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFusion32
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCentTA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCert
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Fin
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Y6F

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

section Certified

theorem yamadaCase3Core_of_basic_inputs_kp (hF : G23Facts)
    (h42 : Sec42) (h44 : Sec44)
    (h52 : Sec52) (h53 : Sec53) (h54 : Sec54) (h55 : Sec55) (h56 : Sec56) (h57 : Sec57)
    (h61 : Sec61) (h62 : Sec62) (h63 : Sec63) (h64a : Sec64a) (h64b : Sec64b)
    (h7 : Sec7False) (h1R : Gomi1RKP) :
    YamadaCase3Core :=
  have h31 : Fusion31 := fusion31_of oddCentre_of outTwo_of
  yamadaCase3Core_of_inputs (settingExists_of hF) (sec4False_of h42 h44)
    (sec5Intro_of (fusion3Def_of h31 oddCentre_of outTwo_of)
      (fusion32_of h31 oddCentre_of outTwo_of) oddCentre_of
      (centTA_of h31 oddCentre_of outTwo_of))
    (sec51_of (fusion3Def_of h31 oddCentre_of outTwo_of)
      (fusion32_of h31 oddCentre_of outTwo_of) oddCentre_of)
    (sec5_of h52 h53 h54 h55 h56 h57) (sec6_of h61 h62 h63)
    (sec64_of h64a h64b) h7 (y6F_of_inputs_kp oddCentre_of h1R)

end Certified

end CFSG.OddStandard.HigherRank.YamadaG23
