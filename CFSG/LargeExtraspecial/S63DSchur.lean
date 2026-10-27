module

public import CFSG.LargeExtraspecial.S63DSchurMain
public import CFSG.LargeExtraspecial.S63DSchurSplit
public import CFSG.LargeExtraspecial.S63CD4

public section

namespace CFSG.LargeExtraspecial.S63


theorem smith58Input_of' (hD : D42CentInput) : Smith58Input :=
  smith58Input_of_split hD d42SplitInput

theorem smith58Input : Smith58Input :=
  smith58Input_of' d42CentInput

end CFSG.LargeExtraspecial.S63
