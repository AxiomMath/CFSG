module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsF42
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsJ2
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsCo1
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsFi22
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsB

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

theorem quasisimpleRankTwoSymplecticInput_of_suz
    (hSuz : SporadicCoverRankInput .Suz) : QuasisimpleRankTwoSymplecticInput :=
  quasisimpleRankTwoSymplecticInput_of_residue f42CoverInput
    ⟨sporadicCoverRankInput_M12, sporadicCoverRankInput_J2, sporadicCoverRankInput_Co1,
      sporadicCoverRankInput_Fi22, hSuz, sporadicCoverRankInput_B⟩

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
