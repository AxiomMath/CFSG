module

public import CFSG.CGT.Stroth77.StrothFrameD
public import CFSG.CGT.Stroth77.StrothAmbient

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

@[expose] def StrothFrame.toAmbient (F : StrothFrame G)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A) : StrothAmbient G where
  S := F.S
  A := F.A
  hAS := F.A_le_S
  dataA := F.dA
  hS_uv := F.uv_mem_S
  hS_t := F.t_mem_S
  hS_u := F.u_mem_S
  hH := hH

@[expose] def StrothFrame.IsD.toDatum {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A) : StrothDatum (F.toAmbient hH) where
  D := D
  hAD := h.A_le
  hDS := h.le_S
  τ := τ
  dataD := dD
  hL := h.L_eq
  hcent := h.cent

end CFSG.CGT.Stroth77
