module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterClassical
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterF4G2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterTwisted
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterReeG2

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.HardMathSupport.Timmesfeld.Coordinator (DefCharOuterRank)

theorem defCharOuterRank_proved : DefCharOuterRank :=
  defCharOuterRank_of_exceptional fun k hk => by
    cases k with
    | E6 => exact defCharOuterRankFamE6
    | E7 => exact defCharOuterRankFamE7
    | E8 => exact defCharOuterRankFamE8
    | F4 => exact defCharOuterRankFamF4
    | G2 => exact defCharOuterRankFamG2
    | twistedE6 => exact defCharOuterRankFamTwistedE6
    | trialityD4 => exact defCharOuterRankFamTrialityD4
    | reeG2 => exact defCharOuterRankFamReeG2
    | _ => exact absurd trivial hk

end CFSG.HardMathSupport.Timmesfeld.DefChar
