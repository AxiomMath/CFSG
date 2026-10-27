module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutR3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiHypOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977


theorem fi24out_closing (h25 : Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [.Fi24Prime] X → 3 ≤ CFSG.pRank 2 X)
    (hI : HypothesisOne (Carrier .Fi24Prime)) :
    ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), FStarSimple N →
      N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi24Prime L →
      SolomonGlobalQ H L K t u → fiOut24 H L K u → False := by
  intro H _ _ N L K t u hN hidx _ hcov hglob hout
  obtain ⟨huN, hunot, hu2, hKL, hKu, hKq, hcard, -⟩ := hout
  have hY : IsSporadic (↥L ⧸ center ↥L) .Fi24Prime := hcov.2.2
  exact fi24out_closing_core hN hcov.1 hcov.2.1 hglob.standardL.1 hglob.cyclicSylow hglob.t_order
    hglob.t_mem hglob.u_comm_t hglob.hyp35 hu2 huN hunot hKL hKu hKq hcard
    (fun _ hν hnot _ hB hperf hcard' => fi24OutR_class_of_isSporadic hY hν hnot hB hperf hcard')
    (fi24_autCenterCond hY) (fi24AutOddCore hY)
    (card_sylow_eq_two_of_oddCover h25 hr hI hN hidx hcov hglob.standardL hglob.cyclicSylow
      hglob.t_mem hglob.t_order)

end CFSG.EvenSporadicStandard.Induction
