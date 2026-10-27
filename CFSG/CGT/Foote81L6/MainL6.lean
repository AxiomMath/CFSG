module

public import CFSG.CGT.Foote81L6.Normalizer.GMain
public import CFSG.CGT.Foote81L6.TStruct.Lemma5Holds
public import CFSG.CGT.Foote81L6.HigmanInput
public import CFSG.CGT.Foote81L6.Fusion3.Holds
public import CFSG.CGT.Foote81L6.TStruct.Lemma4FourHolds
public import CFSG.CGT.Foote81L6.Fusion.Lemma4Holds

public section

namespace CFSG.CGT.Foote81L6

theorem footeMainL6_of_lemmas34
    (h3 : FooteLemma3One) (h3t : FooteLemma3Two) (h41 : FooteLemma4OneLarge)
    (h41w : FooteLemma4OneFour) (h42 : FooteLemma4Two) :
    CFSG.OddStandard.HigherRank.YamadaG23.FooteMainL6 :=
  have h3a : FooteLemma3 := footeLemma3_of_one h3
  have h5 : FooteLemma5 := footeLemma5_holds h3a
  have h5s : FooteLemma5Sylow := footeLemma5Sylow_holds h3a
  footeMainL6_of_inputs h3a (footeNotConjAB_of_one h3) (footeNotConjAAstar_of_two h3t) h41 h41w
    h42 h5 h5s
    (footeLemma8To10_holds higmanHyp_holds (footeNotConjB₀B_of_one h3) h41w h5 h5s)

theorem footeMainL6_holds :
    CFSG.OddStandard.HigherRank.YamadaG23.FooteMainL6 :=
  footeMainL6_of_lemmas34 footeLemma3One_holds footeLemma3Two_holds
    (footeLemma4OneLarge_holds footeLemma3One_holds) (footeLemma4OneFour_holds footeLemma3One_holds)
    (footeLemma4Two_holds footeLemma3One_holds footeLemma3Two_holds)

end CFSG.CGT.Foote81L6
