module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNHostHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.EvenCoverStd

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem twoHSHostHered_of_child7 (h7 : TwoHSGivesHN) (thm24_1 : Sol78Thm24_1Use)
    (inp : Hyp.Thm24ThreeSimpleInputs) (hlie : Hyp.OddLieCompNotSporadic) :
    TwoHSHostHered := by
  intro Y _ _ hY N' hN hidx hkp P hP hPq hZ hHS
  have hev : ¬ Odd (Nat.card ↥(center ↥P)) := by
    rw [hZ]
    decide
  obtain ⟨P', hP', hq', hc, hs'⟩ := exists_cover_in_fStar hN hidx hP hPq hev hHS
  have := hN.isSimpleGroup
  have hkp' : CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥N' :=
    Hyp.kProper_of_section hkp N' (MonoidHom.id ↥N') Function.surjective_id
  have hZ' : Nat.card ↥(center ↥P') = 2 := hc.trans hZ
  have hbal := balance_of_even_cover_at hlie
    (hY ↥N' (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup N')) hN.nonabelian hkp' hP' hs'
    (by rw [hZ']; decide)
  exact h7 ↥N' P' (stdHyp_of_balanced_cover thm24_1 inp hlie (by decide) hN.nonabelian hkp' hbal
    hP' hq' hZ' hs') hZ' hs'

end CFSG.EvenSporadicStandard.Induction
