module

public import Certificates.Data.Kernel.M24G.Steps
public import CFSG.Certificates.Kernel.M24G.ImgSound
public import CFSG.Certificates.Kernel.M24G.ListsSound

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem genTabs_lt : ∀ t ∈ Native.genTabs, ∀ x ∈ t.toList, x < 24 := by decide

theorem trioSteps_eq : Native.genTabs.map Native.imgTrio = trioStepsF := by
  unfold trioStepsF
  refine List.map_congr_left fun t ht => ?_
  funext x
  simp only [Native.imgTrio, imgTrioF, img_eq_imgF t (genTabs_lt t ht)]

theorem sextSteps_eq : Native.genTabs.map Native.imgSext = sextStepsF := by
  unfold sextStepsF
  refine List.map_congr_left fun t ht => ?_
  funext s
  have hf : Native.img t = imgF (imgTab t.toList) := funext (img_eq_imgF t (genTabs_lt t ht))
  simp only [Native.imgSext, imgSextF, sortL_eq_sortN, hf]

end CFSG.KC.M24G
