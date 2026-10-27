module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.GH74.GLS.Stage1.Thm4.Closed

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

theorem ivk_5_1f : IVK_5_1f := by
  intro K _ _ n hK hn8 hn11 u v hu hv huc hvc
  have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt K n := ⟨hK.1, (inferInstance : Finite K), hK.2.1, hK.2.2⟩
  obtain ⟨π, hπ⟩ := CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt hT
  exact hπ.isConj_of_orderOf_eq_two hn8 hn11 hu hv (fun h => huc (hπ.ker_le_center h))
    (fun h => hvc (hπ.ker_le_center h))

end CFSG.GH74.GLS.IVK.Lifted
