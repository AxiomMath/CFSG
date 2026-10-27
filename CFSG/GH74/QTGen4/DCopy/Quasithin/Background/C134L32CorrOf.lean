module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C134L32Corr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin

theorem c134L32Corr_of_F4 (hcorr : MS93.AS_C_1_34_corr_F4) : C134L32Corr_F4 := by
  intro G _ _ G₀ R L hMS hL hG hα
  obtain ⟨F, iF, fF, α, hF2, hαm⟩ := hα
  obtain ⟨i, hi⟩ := hcorr G G₀ R L hMS hL hG ⟨1, F, iF, fF, α, by rw [hF2]; norm_num, hαm⟩
  match i, hi with
  | 0, hi => exact hi.elim
  | 1, hi => exact ⟨1, hi⟩
  | 2, hi => exact ⟨2, hi⟩
  | 3, hi => exact ⟨3, hi⟩
  | 4, hi => exact ⟨4, hi⟩
  | 5, hi => exact ⟨5, hi⟩
  | _ + 6, hi => exact hi.elim

end CFSG.Quasithin
