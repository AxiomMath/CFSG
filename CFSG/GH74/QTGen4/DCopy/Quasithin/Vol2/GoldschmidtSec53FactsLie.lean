module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsLie
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Facts533
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3PerType
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsThree

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem stmt5_3_3_factsAt_of_lieFacts_F4 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (ht : t ≠ .PSp) (hL : LieFactsAt t m) (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (h532 : Stmt5_3_2At_F4 t m) : Stmt5_3_3_factsAt_F4 t m := by
  obtain ⟨hM, hA⟩ := hL
  intro G _ _ T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨Y, _, hY, TY, M₁, M₂, hpair, ⟨Φ⟩⟩ := hty.1
  obtain ⟨hfin, hT⟩ := hM Y f hpar hY
  obtain ⟨Y', _, hY', hE⟩ := h532 G T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hE
  obtain ⟨hfin', hT'⟩ := hM Y' f hpar hY'
  have : Finite Y' := hfin'
  obtain ⟨-, hP, hU1, -⟩ := hT' E.TD E.P1 E.P2 E.yam
  have hX := hA Y' f hpar hY' E.toLieAmalgamExt hP hU1
  have hii := facts_ii_F4 Φ h527 hyp hty (hT TY M₁ M₂ hpair).1
  exact ⟨facts_i_of_ext_finY_F4 h531 hyp hty hpar E ⟨hX.1, hX.2⟩, hii.1, hii.2, fun h => absurd h ht⟩

end CFSG.Quasithin.H13.Sec53F
