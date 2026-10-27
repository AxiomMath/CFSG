module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Psl

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem core911_l5 : Core911L5 := by
  intro Y _ _ _ _ h
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  exact no911_psl (by norm_num) hp2 hL hp hf

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
