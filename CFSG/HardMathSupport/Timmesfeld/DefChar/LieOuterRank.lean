module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterFamilies
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwistedAC
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterOrth
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.HardMathSupport.Timmesfeld.Coordinator (LieOuterRank)

theorem lieOuterRank_proved : LieOuterRank :=
  lieOuterRank_of_families fun k => by
    cases k with
    | A => exact lieOuterRankFam_A
    | twistedA => exact lieOuterRankFamTwistedA
    | B => exact lieOuterRankFamB
    | C => exact lieOuterRankFamC
    | D => exact lieOuterRankFamD
    | twistedD => exact lieOuterRankFamTwistedD
    | E6 => exact lieOuterRankFamE6
    | E7 => exact lieOuterRankFamE7
    | E8 => exact lieOuterRankFamE8
    | F4 => exact lieOuterRankFamF4
    | G2 => exact lieOuterRankFamG2
    | twistedE6 => exact lieOuterRankFamTwistedE6
    | trialityD4 => exact lieOuterRankFamTrialityD4
    | suzuki => exact lieOuterRankFamSuzuki
    | reeG2 => exact lieOuterRankFamReeG2
    | reeF4 => exact lieOuterRankFamReeF4
    | tits => exact lieOuterRankFamTits

end CFSG.HardMathSupport.Timmesfeld.DefChar
