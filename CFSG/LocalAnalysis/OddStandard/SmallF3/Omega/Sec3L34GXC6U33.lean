module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Def
public import Certificates.Certificate442271
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Aut
import CFSG.GH74.KGroups.U33
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.GH74.KGroups


theorem l34g_c6_U33 {Y : Type} [Group Y] (hY : LieModel Y .PSU 3 3 1) : L34GC6 Y := by
  obtain ⟨e⟩ := U33.equiv_of_lieModel hY
  obtain ⟨M, hP, hA⟩ := U33.autModel e
  have hs := c6free_sound U33.QA U33.QP U33.QA_ok U33.QP_ok Certificates.certificate442271
  refine l34g_c6_of_autModel M fun τ hτ hτ2 y hy u hu => ?_
  exact hs τ (hA ▸ hτ) hτ2 y (hP ▸ hy) u (hP ▸ hu)

end CFSG.OddStandard.SmallF3.Omega
