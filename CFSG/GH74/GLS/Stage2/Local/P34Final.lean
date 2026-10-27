module

public import CFSG.GH74.GLS.Stage2.Local.P34Main4
public import CFSG.GH74.GLS.Stage2.Local.P34M12Thm
public import CFSG.GH74.GLS.Stage2.Local.P34OneFinal
public import CFSG.GH74.GLS.Stage2.Local.GHSchMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Done
public import CFSG.GH74.GLS.Stage2.Local.Prop27WProvedCtx

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open CFSG.GH74.GLS.IVK.Proofs2

theorem leaf_prop34_of_prop27W
    (h27 : Leaf_Prop27W Stage2Ctx0) : Leaf_Prop34 :=
  leaf_prop34_final'' (Ctx := Stage2Ctx0) (fun _ _ _ _ _ _ h => h.toCtx0) ivk93_proved P34M12.prop34M12_thm noOneClassC0'
    (fun J _ _ hJ hn hG => by have := hJ; exact GHSch.ghSchreier_thm J hn hG)
    (fun _ _ _ _ _ _ ctx h => ctx.rank_three h) h27 ivk93KindM12_proved P34NS.m12Facts

theorem leaf_prop34_proved
    : Leaf_Prop34 :=
  leaf_prop34_of_prop27W
    (leaf_prop27W_ctx0 (fun J _ _ hJ hn hG => by have := hJ; exact GHSch.ghSchreier_thm J hn hG))

end CFSG.GH74.GLS.Stage2.Local.P34
