module

public import CFSG.CGT.PushingUpLit.A78T2.Final
public import CFSG.CGT.PushingUpLit.A78L3.Two
public import CFSG.CGT.PushingUpLit.A78L3.FromCfg

public section

namespace CFSG.CGT.PushingUpLit.A78

theorem threeSNonSylow_of_data (hT2From : A78T2.T2FromCfg) (hSp4From : A78Sp4.Sp4FromCfg) :
    Aschbacher78ThreeSNonSylow :=
  threeSNonSylow_of_split (A78T2.nonSylowL3_of_cut hT2From A78T2.t2Chain A78L3.t2Two)
      (A78Sp4.nonSylowSp4GE3_of_cut hSp4From A78Sp4.sp4ChainGE3)
      (A78Sp4.nonSylowSp4Two_of_cut hSp4From A78Sp4.sp4ChainTwo)

theorem threeSNonSylow_of_sp4 (hSp4From : A78Sp4.Sp4FromCfg) : Aschbacher78ThreeSNonSylow :=
  threeSNonSylow_of_data A78L3.t2FromCfg hSp4From

end CFSG.CGT.PushingUpLit.A78
