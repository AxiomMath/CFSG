module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

section Tits


theorem crossCharTwoFamCat_tits : CrossCharTwoFamCat .tits := by
  rintro ⟨d, hv⟩ hd p hp hp5 _ _ D hD hcard H hH hDH
  have hd' : d = .tits := hd
  subst hd'
  exact (CFSG.LieType.SeitzGeneration.no_plane_tits hv hp (by omega) (by omega) (by omega)
    (E := D) hcard).elim

end Tits

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
