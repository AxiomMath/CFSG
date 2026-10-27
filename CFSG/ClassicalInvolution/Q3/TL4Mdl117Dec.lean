module

public import Certificates.Data.GH74.AE117

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open Certificates.AE117

theorem cocProp₅_of (h : cocCheck₅ () = true) : cocProp g₁₅ g₂₅ rels₅ := of_decide_eq_true h

theorem cocProp₆_of (h : cocCheck₆ () = true) : cocProp g₁₆ g₂₆ rels₆ := of_decide_eq_true h

theorem cocProp₇_of (h : cocCheck₇ () = true) : cocProp g₁₇ g₂₇ rels₇ := of_decide_eq_true h

theorem genProp₅_of (h : genCheck₅ () = true) : genProp g₁₅ g₂₅ words₅ := of_decide_eq_true h

theorem genProp₆_of (h : genCheck₆ () = true) : genProp g₁₆ g₂₆ words₆ := of_decide_eq_true h

set_option maxRecDepth 4000 in
theorem genProp₇_of (h : genCheck₇ () = true) : genProp g₁₇ g₂₇ words₇ := of_decide_eq_true h

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
