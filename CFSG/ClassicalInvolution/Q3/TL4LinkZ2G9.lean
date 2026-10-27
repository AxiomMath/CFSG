module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W11
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G1
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G2
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Model
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

theorem z2GapFacts_of_certs :
    Z2GapFacts :=
  ⟨gapTwinE4Sp62_of_certs, gapTwinE4O8p2_of_certs, gapOmegaSmall_of_certs,
    orthThreeCommutingFacts_proved, gapOmegaL43_of_certs⟩

theorem tightLinkZ2L2OuterR_plus
    (n : ℕ) : TL4.PlusLeaf TL4.TightLinkZ2L2OuterR n :=
  tightLinkZ2L2OuterR_plus_of_gaps z2GapFacts_of_certs n

theorem tightLinkZ2L2InnerR_plus
    (n : ℕ) : TL4.PlusLeaf TL4.TightLinkZ2L2InnerR n :=
  tightLinkZ2L2InnerR_plus_of_gaps z2GapFacts_of_certs n

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
