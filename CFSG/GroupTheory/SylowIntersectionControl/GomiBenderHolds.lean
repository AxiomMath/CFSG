module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.GroupTheory

theorem gomiBender_holds : GomiBender :=
  fun X _ _ H hH => CFSG.Open.bender_strongly_embedded_normal_series X H hH

end CFSG.GroupTheory
