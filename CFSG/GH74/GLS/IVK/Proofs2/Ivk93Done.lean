module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Proved
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Proved2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Psp4G
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sp4Swap
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93McLG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93LyG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeavesProved
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Final

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local.P34

theorem ivk93_proved






























    : IVK93 := by
  have h93 := ivk93Pair_proved
  have h93' := ivk93Pair2_proved
  have hswap : Ivk93Adapt.Psp4Swap := by
    intro J _ _ q q₁ q₂ hq h5 hK x L₁ L₂ h P hxP hxc
    exact psp4_swap hq h5 hK h P hxP hxc
  refine ivk93_of_kinds fun k => ?_
  cases k with
  | m12 => exact (ivk93KindM12_proved).toKind
  | psp4 =>
    exact fun _ _ _ _ _ hctx _ hne hCH _ hs hn hPerf _ =>
      Or.inr (Ivk93Adapt.ivk93_psp4 h93 hctx hne hCH hs hn hPerf)
  | l4 _ =>
    exact fun _ _ _ _ _ hctx _ hne hCH hV hs hn hPerf h2 =>
      Ivk93Adapt.ivk93_l4 h93 Ivk93Adapt.ivk93OneClassRes_proved hctx hne hCH hV hs hn hPerf h2
  | g2 =>
    exact fun _ _ _ _ _ hctx _ hne hCH hV hs hn hPerf h2 =>
      Or.inr (Ivk93Adapt.ivk93_g2_of_swap h93' Ivk93Adapt.ivk93_res3_proved hswap hctx hne hCH hV
        hs hn hPerf h2)
  | mcl => exact ivk93Kind_mcl
  | ly => exact ivk93Kind_ly

end CFSG.GH74.GLS.IVK.Proofs2
