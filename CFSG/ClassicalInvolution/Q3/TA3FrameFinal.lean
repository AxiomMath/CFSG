module

public import CFSG.ClassicalInvolution.Q3.TA3FrameAll
public import CFSG.ClassicalInvolution.Q3.TA3FrameL3U3
public import CFSG.ClassicalInvolution.Q3.TA3FrameL4b
public import CFSG.ClassicalInvolution.Q3.TA3FrameU4
public import CFSG.ClassicalInvolution.Q3.TA3FrameU5
public import CFSG.ClassicalInvolution.Q3.TA3FrameL34
public import CFSG.ClassicalInvolution.Q3.TA3FrameD43

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS

theorem frameParts_proved : FrameParts where
  l3 := fun _ _ _ _ ⟨_, _, hp, hp2, h5, hm⟩ t ht => layerExcludesQ8_l3 hp hp2 h5 hm t ht
  u3 := fun _ _ _ _ ⟨_, _, hp, hp2, h5, hm⟩ t ht => layerExcludesQ8_u3 hp hp2 h5 hm t ht
  l4 := fun _ _ _ _ ⟨_, _, hp, hp2, h5, h8, hm⟩ t ht => layerExcludesQ8_l4 hp hp2 h8 h5 hm t ht
  u4 := fun _ _ _ _ ⟨_, _, hp, hp2, h5, h8, hm⟩ t ht => layerExcludesQ8_u4 hp hp2 h8 h5 hm t ht
  l5 := fun _ _ _ hF ⟨_, _, hp, hp2, h5, _, hm⟩ t ht => layerExcludesQ8_l5 hF hp hp2 h5 hm t ht
  u5 := fun _ _ _ hF ⟨_, _, hp, hp2, h5, _, hm⟩ t ht => layerExcludesQ8_u5 hF hp hp2 h5 hm t ht
  l34 := fun _ _ _ _ _ _ hS h3 _ hT => by
    have := hS.normal
    exact false_of_l34 hS.member hS.sup h3 hS.cent hT
  d43 := fun _ _ _ _ _ _ hS h3 _ hT => by
    have := hS.normal
    exact false_of_d43 hS.member hS.sup h3 hS.cent hT

theorem residualCFrameSmall_of_gh74 (hGH : GH74SectionalModels) : ResidualCFrameSmall :=
  residualCFrameSmall_of_parts hGH frameParts_proved

end CFSG.ClassicalInvolution.Q3.TA3.Frame
