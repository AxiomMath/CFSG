module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Facts533
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3PerType
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpExt

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13.F431

theorem stmt5_3_3_factsAt_PSp_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (h532 : Stmt5_3_2At_F4 .PSp 2) : Stmt5_3_3_factsAt_F4 .PSp 2 := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨P, _, _, N₁, N₂, hT, hS, ⟨Φ⟩⟩ := exists_sp_facts hty
  obtain ⟨Y, _, hY, hE⟩ := h532 G T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hE
  have : Finite Y := finite_of_lieModel_psp hY
  have hii := facts_ii_F4 Φ h527 hyp hty hT
  refine ⟨facts_i_of_ext_finY_F4 h531 hyp hty hpar E (extFacts_sp hY E), hii.1, hii.2,
    fun _ u hu hord => ?_⟩
  refine facts_iii_F4 Φ h527 hyp hty hT hS u hu ?_
  rintro rfl
  rw [orderOf_one] at hord
  exact absurd hord (by norm_num)

end CFSG.Quasithin.H13.Sec53F
