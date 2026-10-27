module

public import CFSG.ClassicalInvolution.Q3.TA3FrameExcl
public import CFSG.ClassicalInvolution.Q3.TA3FrameSplit
public import CFSG.ClassicalInvolution.Q3.TA3SmallBase

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS

theorem residualCFrameSmall_of_parts (hGH : GH74SectionalModels) (hP : FrameParts) :
    ResidualCFrameSmall := by
  intro Y _ _ _ z L T hS _ h3 _ hF
  have := hS.normal
  obtain ⟨hTs, hnab⟩ := simple_of_isComponentOf_cent hS.comp hS.cent
  obtain ⟨eF⟩ := nonempty_genFittingFStar_equiv ↥T hnab
  have hF' : TwoSubgroupsFourGenerated ↥T :=
    twoSubgroupsFourGenerated_of_surjective eF.toMonoidHom eF.surjective hF
  rcases smallList hGH ↥T hnab hF' with h | h
  · exact false_of_smallFamily hP hS h3 hF' h
  · exact false_of_excludedSmall hP.l34 hS h3 hF' h

end CFSG.ClassicalInvolution.Q3.TA3.Frame
