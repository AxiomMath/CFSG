module

public import CFSG.GH74.GLS.Stage2.Local.Prop27WProved

public section

namespace CFSG.GH74.GLS.Stage2.Local

theorem leaf_prop27W_ctx0
    (hSch : P34.GHSchreier) : Leaf_Prop27W Stage2Ctx0 :=
  leaf_prop27W_of_ctx (fun _ _ _ _ _ _ h => h.detail.l4_two) (fun _ _ _ _ _ _ h => h.data)
    (fun _ _ _ _ _ _ h => h.central) (fun _ _ _ _ _ _ h => h.sylow)
    (fun _ _ _ _ _ _ h => h.std.kgh) (fun _ _ _ _ _ _ h => h.detail) hSch

end CFSG.GH74.GLS.Stage2.Local
