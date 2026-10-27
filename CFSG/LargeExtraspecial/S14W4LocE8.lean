module

public import CFSG.LargeExtraspecial.S14W4LocNoA2
public import CFSG.LargeExtraspecial.O62Weak

public section

namespace CFSG.LargeExtraspecial.S14.W4Loc

theorem weaklyClosedE8Stmt : WeaklyClosedE8Stmt := by
  intro V _ _ _ q hV hq H E h1 h2 hEH hE8 hab hinv hwc
  exact O62.weaklyClosed_E8 hV hq h1 h2 hEH hE8 hab hinv hwc

end CFSG.LargeExtraspecial.S14.W4Loc
