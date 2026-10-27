module

public import CFSG.LargeExtraspecial.SMod20RhoCheck

public section

namespace CFSG.SmithE

@[expose] def chkDist2 : Bool :=
  (List.range 891).all fun i =>
    ((List.range 891).filter fun j => meetCard i j == 1).length == 336

end CFSG.SmithE
