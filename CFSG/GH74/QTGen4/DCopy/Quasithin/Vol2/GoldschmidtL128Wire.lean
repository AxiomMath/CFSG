module

public import CFSG.Quasithin.Vol2.GoldschmidtL128Wire
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneTwelve

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

open L128P

theorem lemma12_8_12_two_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) : Lemma12_8_12_two_F4 := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  have S := setting128A_F4 h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, hTZ⟩ := T_le_normalizer_w128_F4 h1222 h12213 hs
  rw [hkY _ hTW, hkY _ hTZ]
  exact L128A.twelve_two_of_eq S ⟨hk, hkN⟩ (uA_eq_F4 h1222 hs)

theorem lemma12_8_11_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) : Lemma12_8_11_F4 := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  have S := setting128A_F4 h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, -⟩ := T_le_normalizer_w128_F4 h1222 h12213 hs
  rw [hkY _ hTW]
  exact L128A.eleven_of_eq S ⟨hk, hkN⟩ (uA_eq_F4 h1222 hs)

theorem lemma12_8_11_hat_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) : Lemma12_8_11_hat_F4 := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN a ha haV₁ D
  have S := setting128A_F4 h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, hTZ⟩ := T_le_normalizer_w128_F4 h1222 h12213 hs
  rw [hkY _ hTW, hkY _ hTZ]
  exact L128A.hat_of_g111 (L128A.g111_of_eq S ⟨hk, hkN⟩ (uA_eq_F4 h1222 hs) D
    (four_lt_relIndex_F4 h1222 h12213 hs) ha haV₁)

end CFSG.Quasithin.H13
