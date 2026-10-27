module

public import CFSG.CGT.Foote81L6.TStruct.Lemma5
public import CFSG.CGT.Foote81L6.MainL6Inputs

public section

namespace CFSG.CGT.Foote81L6

theorem footeLemma5_holds (h3 : FooteLemma3) : FooteLemma5 := fun G _ _ T m n D =>
  D.lemma5 (h3 G T m n D)

theorem footeLemma5Sylow_holds (h3 : FooteLemma3) : FooteLemma5Sylow := fun G _ _ T m n D =>
  D.sylow_normalizer_E64 (h3 G T m n D)

end CFSG.CGT.Foote81L6
