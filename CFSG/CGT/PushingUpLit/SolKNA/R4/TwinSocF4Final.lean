module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Main

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

section Small

theorem model163R_holds (r : ℕ) : Perp22Rest.Model163R r :=
  model163R_of_socF4 (socF4L3_holds r) (socF4U3_holds r)

end Small

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
