module

public import CFSG.ClassicalInvolution.Q3.TL4LinkLie
public import CFSG.ClassicalInvolution.Q3.TL4OddLieCover
public import CFSG.ClassicalInvolution.Q3.TL4OddLieZ2
public import CFSG.ClassicalInvolution.Q3.TL4OddLieTwo
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Gen
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Hyp

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic


theorem tightLinkLieR_three_of_star {n : ℕ} (hS : TightLinkStarEdgeR 3 n) : TightLinkLieR 3 n :=
  tightLinkLieR_of hS lieKindTwoNbrs_proved lieKindE4Edge_proved lieKindE4Cover_proved
    lieKindZ2NoStar_proved

end CFSG.ClassicalInvolution.Q3.TL4
