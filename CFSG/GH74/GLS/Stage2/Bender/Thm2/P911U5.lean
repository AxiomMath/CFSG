module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Psu

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem core911_u5 : Core911U5 := by
  intro Y _ _ _ _ h
  obtain ⟨p, f, -, hf, hq, hL⟩ := h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  exact no911_psu (by norm_num) hp2 hL

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
