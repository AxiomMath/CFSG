module

public import CFSG.CGT.Foote82.T66.Main
public import CFSG.CGT.Foote82.TheoremG
public import CFSG.CGT.Foote82.EF1
public import CFSG.CGT.Foote82.D1

public section

namespace CFSG.CGT.Foote82

theorem footeLeavesF_of_named
    (h : Thm66Named) : FooteSixF ∧ FooteFiveF ∧ FooteSevenSharpF :=
  ⟨footeSixF_of_thm66F (thm66F_of_named h), footeFiveF_of_thm66F (thm66F_of_named h),
    footeSevenSharpF_of_thm66F (thm66F_of_named h)⟩

end CFSG.CGT.Foote82
