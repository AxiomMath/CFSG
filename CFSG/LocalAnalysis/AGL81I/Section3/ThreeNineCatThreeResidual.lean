module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeUnitaryTwo
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThree
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz12

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

theorem crossCoverResidualE6Three_holds :
    CrossCoverResidualE6Three := by
  intro X _ _ K E d hKn hKq h3 ⟨e⟩ hres hE hEc hrk
  exfalso
  obtain ⟨d, hv⟩ := d
  cases d
  case twistedE6 q =>
    obtain ⟨hq2, hq13⟩ := hres
    have hmod : q.card % 3 = 2 := by
      rw [PrimePower.card_def, hq2]
      rcases hq13 with h | h <;> rw [h] <;> norm_num
    have h6 :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz12.six_le_pRank_of_twistedE6Cover
        hmod e h3
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
      exact (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left).trans hrk
    omega
  all_goals exact hres.elim

theorem crossCoverResidual24_12Three_holds :
    CrossCoverResidual24_12Three :=
  crossCoverResidual24_12Three_of_e6 crossCoverResidualE6Three_holds

theorem catalogue24_12Three_of_sporadicGen
    (hSG : SporadicGen24_12Three) : Catalogue24_12Three :=
  catalogue24_12Three_of hSG crossCoverResidual24_12Three_holds

end CFSG.LocalAnalysis.AGL81I.Section3
