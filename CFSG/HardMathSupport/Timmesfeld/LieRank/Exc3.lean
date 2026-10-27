module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7
public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2
public import CFSG.HardMathSupport.Timmesfeld.LieRank.U43
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverSplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank

section Certificates


theorem lieCoverRankHighExc3_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    Tables.T1b.LieCoverRankHighExc3 := by
  rintro L _ _ hq - p - - hdvd h3 ⟨rfl, t, n, r, f, ht, hm⟩
  rcases ht with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · have := pRank_le_two_of_lieModel_PSL_two_three_two hm
    omega
  · obtain ⟨e⟩ := nonempty_mulEquiv_openOmega_of_lieModel hm
    have hc := statedClassicalModel_of_lieModel (by decide) (by decide) (by decide) hm
    have hZ := Tables.Multiplier.center_dvd_table hGA (Tables.T1b.isQuasisimple_of_open' hq)
      (MulEquiv.refl _) (Tables.Multiplier.lieModel_of_classical hc)
    have h6 : Nat.card (Subgroup.center L) ∣ 6 := hZ
    exact O7.pRank_quotient_le_of_cover_O7 hq e hdvd h6
  · obtain ⟨e⟩ := nonempty_mulEquiv_adjointGroup_G2_of_lieModel hm
    exact pRank_quotient_le_of_cover_G2 e hdvd
  · obtain ⟨e⟩ := nonempty_mulEquiv_X₀_of_lieModel hm
    exact pRank_quotient_le_of_cover_U43 e hdvd

end Certificates

end CFSG.HardMathSupport.Timmesfeld.LieRank
