module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Def
public import Certificates.Certificate442270
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Aut
import CFSG.GH74.KGroups.L33

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.GH74.KGroups


theorem l34g_c6_L33 {Y : Type} [Group Y] (hY : LieModel Y .PSL 3 3 1) : L34GC6 Y := by
  obtain ⟨e⟩ := L33.equiv_of_lieModel hY
  obtain ⟨M, hP, hA⟩ := L33.autModel e
  have hs := c6free_sound L33.QA L33.QP L33.QA_ok L33.QP_ok Certificates.certificate442270
  refine l34g_c6_of_autModel M fun τ hτ hτ2 y hy u hu => ?_
  exact hs τ (hA ▸ hτ) hτ2 y (hP ▸ hy) u (hP ▸ hu)

end CFSG.OddStandard.SmallF3.Omega
