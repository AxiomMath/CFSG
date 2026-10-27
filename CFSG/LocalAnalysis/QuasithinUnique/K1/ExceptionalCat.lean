module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatG2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTriality
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatRee
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTits
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.QuasithinUnique.K1

theorem k1_exceptional
    (hX : TitsNoStronglyClosedElemAbelian)
    (hA : TitsSylowCentralizingAutInner) : K1FamilyRecognition ExceptionalFamilyCat := by
  intro G _ _ H S U L h hfam w hwU hwS hnc _
  rcases hfam with ⟨f, hg2 | htri | hree | hsz⟩ | htits
  · exact absurd (centralizes_of_g2 h hg2.1 hg2.2 hwU hwS) hnc
  · exact absurd (centralizes_of_triality h htri.1 htri.2 hwU hwS) hnc
  · exact absurd (centralizes_of_ree h hree.2.2 hwU hwS) hnc
  · exact fusionIsBenderGroup_of_suzukiModel hsz.2.2
  · exact absurd (centralizes_of_tits hX hA h htits hwU hwS) hnc

end CFSG.QuasithinUnique.K1
