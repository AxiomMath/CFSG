module

public import CFSG.GH74.GLS.C3.Prop121.Main
public import CFSG.GH74.GLS.C3.Prop121.StageA
public import CFSG.GH74.GLS.C3.Prop121.Derive
public import CFSG.GH74.GLS.C3.Prop121.G5

public section

namespace CFSG.GH74.GLS.C3.Prop121

open CFSG.GH74.GLS

theorem s_prop121_cfg_of_core
    (hG5 : S_gFive) (hB : S_lemma123_core) : S_prop121_cfg :=
  s_prop121_cfg_of_parts (s_stage3Loc_of hG5) (s_lemma123_of_core hB)

theorem s_gFive
    : S_gFive := fun _ _ _ hC _ _ _ _ _ _ h hA => exists_g_five hC h hA

theorem s_prop121_cfg_of
    (hB : S_lemma123_core) : S_prop121_cfg :=
  s_prop121_cfg_of_core s_gFive hB

end CFSG.GH74.GLS.C3.Prop121
