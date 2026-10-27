module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.HardMathSupport.Curtis.Proving.E27RankKill

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.HardMathSupport.Foote.E27 CFSG.LieType.SeitzGeneration TauCeti
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Curtis.Proving


theorem false_of_exc_cross_reeF4 {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid)
    (e : Nonempty (↥K ≃* (CFSGIndex.lie ⟨LieTypeIndex.reeF4 m, hv⟩).Group)) : False := by
  obtain ⟨e⟩ := e
  exact false_of_E27_rankLE2 h hz
    (RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_three_cat_reeF4 hv))

end CFSG.HardMathSupport.Curtis.UnitaryLevi
