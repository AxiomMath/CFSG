module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA1
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreOrth
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreF4G2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreReeD4
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.HardMathSupport.Timmesfeld.Coordinator
  (DefCharInnerCoreFree LocalThreeBalanceDefChar localThreeBalanceDefChar_of)

theorem defCharInnerCoreFreeFamA : DefCharInnerCoreFreeFam .A := by
  intro S _ _ hS hnab idx hk hidx p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hrq⟩ := hk
  have hv := idx.2
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hrq] at hv
  have hr1 : 1 ≤ r := hv.1.1
  by_cases hr : r = 1
  · exact defCharInnerCoreFreeFamA_one S hS hnab idx ⟨q, hrq.trans (by rw [hr])⟩ hidx p hp hp2
      hch x hx hxo H hH
  · exact defCharInnerCoreFreeFamA_of_two_le S hS hnab idx ⟨r, q, hrq, by omega⟩ hidx p hp hp2 hch
      x hx hxo H hH

theorem defCharInnerCoreFree_of_dFour (h4 : DefCharInnerCoreFreeFamDFour) :
    DefCharInnerCoreFree :=
  defCharInnerCoreFree_of_families fun k => by
    cases k with
    | A => exact defCharInnerCoreFreeFamA
    | twistedA => exact defCharInnerCoreFreeFamTwistedA
    | B => exact defCharInnerCoreFreeFamB
    | C => exact defCharInnerCoreFreeFamC
    | D => exact defCharInnerCoreFreeFamD_of_four h4
    | twistedD => exact defCharInnerCoreFreeFamTwistedD
    | E6 => exact defCharInnerCoreFreeFamE6
    | E7 => exact defCharInnerCoreFreeFamE7
    | E8 => exact defCharInnerCoreFreeFamE8
    | F4 => exact defCharInnerCoreFreeFamF4
    | G2 => exact defCharInnerCoreFreeFamG2
    | twistedE6 => exact defCharInnerCoreFreeFamTwistedE6
    | trialityD4 => exact defCharInnerCoreFreeFamTrialityD4
    | reeG2 => exact defCharInnerCoreFreeFamReeG2

theorem localThreeBalanceDefChar_of_dFour (h4 : DefCharInnerCoreFreeFamDFour) :
    LocalThreeBalanceDefChar :=
  localThreeBalanceDefChar_of defCharOuterRank_proved (defCharInnerCoreFree_of_dFour h4)

end CFSG.HardMathSupport.Timmesfeld.DefChar
