module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiHypOne

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem fi23TwoSylow_of (h25 : Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [.Fi23] X → 3 ≤ CFSG.pRank 2 X)
    (hI : HypothesisOne (Carrier .Fi23)) : Fi23TwoSylow := by
  intro H _ _ N L K t u hN hidx _ hcov hglob _
  exact card_sylow_eq_two_of_oddCover h25 hr hI hN hidx hcov hglob.standardL hglob.cyclicSylow
    hglob.t_mem hglob.t_order

end CFSG.EvenSporadicStandard.Induction
