module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VVertex
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeGH
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.CGT.PushingUpLit.SolKNA.R4

section Main

theorem vertexEdgelessExclR_holds_of_gh74 (hGH : GH74SectionalModels) {r : ℕ} (hr : 4 ≤ r) (n : ℕ) :
    Perp24.VertexEdgelessExclR r n :=
  vertexEdgelessExclR_of_inputs2 (smallListR_of_gh74 hGH) (noDatumOtherR_holds r)
    (tightLargeEdgeSR_holds hr) (socF4L3_holds r) (socF4U3_holds r)

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
