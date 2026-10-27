module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSpor
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Milestones.FAM_M_finiteness

public section

namespace CFSG.AGLEmbedding

theorem kFactP1ThreeSpor :
    KFactP1ThreeSpor := by
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  exact kFactP1ThreeSpor_of hbr (not_dvd_card_outer_sporadic hbr) CFSG.Milestones.fam_m_finiteness

end CFSG.AGLEmbedding
