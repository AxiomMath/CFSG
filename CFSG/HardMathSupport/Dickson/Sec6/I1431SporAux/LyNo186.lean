module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Order62
public import CFSG.Sporadic.Schreier.LyR3EFusion

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint CFSG.Sporadic.LySchreier

section Ly


theorem noOrder186_JLy : NoOrder 186 ↥CFSG.Sporadic.Ly.J := by
  refine noOrder186_of_involution_centralizers fun t ht => ?_
  obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 t ht
  have hc : IsConj (lyz : CFSG.Sporadic.Ly.J) t := isConj_iff.2 ⟨x, hx⟩
  have h2 := full_involution_centralizer.2
  rw [card_centralizer_of_isConj hc, h2]
  norm_num

theorem noOrder186_Ly : NoOrder 186 NativeSporadic.Ly := fun g hg =>
  noOrder186_JLy (CFSG.Sporadic.Ly.lyEquivJ g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end Ly

end CFSG.HardMathSupport.Dickson.Sec6.I1431
