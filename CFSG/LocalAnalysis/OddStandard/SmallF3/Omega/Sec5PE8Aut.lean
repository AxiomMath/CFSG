module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Small
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8PslMain

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5pe8_aut_statement :
    Sec5PE8AutStatement := by
  intro Y _ _ P hP hshape tb htb htb2 htbc κ hodd hκP hfix
  rcases hshape with h | h | h | ⟨F, _, _, J, hJ⟩
  · exact sec5pe8_small P hP (Or.inl h) κ hodd hκP
  · exact sec5pe8_small P hP (Or.inr (Or.inl h)) κ hodd hκP
  · exact sec5pe8_small P hP (Or.inr (Or.inr h)) κ hodd hκP
  · exact sec5pe8_psl2_trivial P hJ htb htb2 htbc κ hodd hκP fun w _ hw hc => hfix w hw hc

end CFSG.OddStandard.SmallF3.Omega
