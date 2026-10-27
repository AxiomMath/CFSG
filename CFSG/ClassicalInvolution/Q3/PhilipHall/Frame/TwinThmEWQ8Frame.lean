module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmQ8Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Conv


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem MinCexQ8.toFrame (c : MinCexQ8 Ω K S R W H) :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.MinCexQ8Frame Ω K S R W H :=
  ⟨c.stand.hyp, c.stand.mem, c.stand.hR, c.stand.hW, c.stand.twin, c.stand.q8, c.hyp.trans⟩

end Conv

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
