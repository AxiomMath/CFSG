module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InnerIsoE6
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6HeisScBase

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree


theorem e6InnerIsotropic_of_frame (h : ExcWideThree.E6HeisFrameNormalizesR) :
    E6InnerIsotropic :=
  e6InnerIsotropic_of_frame_of_scBase
    (fun {_ _} [_] [_] [_] [_] ι => ExcWideThree.exists_scBaseChange ι) h

end CFSG.LieType.SeitzGeneration.ExcHighThree
