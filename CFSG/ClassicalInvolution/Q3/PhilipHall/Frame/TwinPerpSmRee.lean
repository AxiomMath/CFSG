module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallRee

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ComponentClassification.LiteratureLocal
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall


theorem leaf_twistedG2 {n : ℕ} : TwinLeafS n SmallTwistedG2 :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hF => by
    haveI := h.core.simple
    obtain ⟨f, hm⟩ := hF
    rcases hm with ⟨htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, -, hree⟩ | ⟨-, htag, -⟩
    · exact absurd htag (by decide)
    · exact absurd htag (by decide)
    · obtain ⟨-, -, -, -, -, h3⟩ := hree.1
      obtain ⟨a, hea, -⟩ := hree.2
      subst hea
      obtain ⟨-, -, -, -, -, -, hodd⟩ :=
        ward_kleidman_small_Ree_involution_centralizer_maximal a (by omega) _ hree
      exact false_of_outTwoCyclic_of_noTwinPair h (outTwoCyclic_of_odd hodd)
        (not_twinPair_of_twinCyc4 (twinCyc4_twistedG2 hree))
    · exact absurd htag (by decide)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
