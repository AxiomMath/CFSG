module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiRowParts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiGiven
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCfg610
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22Closing
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Row
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Reduce
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutRow

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

structure FiInputs : Prop where
  lemma25 : Finkelstein77.Asc76Lemma25
  rank22 : ∀ (X : Type) [Group X], IsLS [.Fi22] X → 3 ≤ CFSG.pRank 2 X
  rank23 : ∀ (X : Type) [Group X], IsLS [.Fi23] X → 3 ≤ CFSG.pRank 2 X
  rank24 : ∀ (X : Type) [Group X], IsLS [.Fi24Prime] X → 3 ≤ CFSG.pRank 2 X
  hypOne23 : HypothesisOne (Carrier .Fi23)
  hypOne24 : HypothesisOne (Carrier .Fi24Prime)
  mult23 : OddMultTrivial .Fi23
  lemma63 : Fi23Lemma63
  lemma65 : Balance.Sol78Lemma65KP
  balance23 : Fi23BalanceHered
  claim612E : Fi23Claim612EHered
  tail23 : Fi23TailHered
  cfg610 : Fi24Cfg610Hyp35
  noStdFi22 : Fi24NoStdFi22

theorem FiInputs.closing (h : FiInputs) : Sol78ClosingFi :=
  sol78ClosingFi_of_parts (sol78Closing_fi22 h.lemma25 h.rank22)
    (fun H _ _ hH N L K t u s hs hN hidx hKP hcov hglob hpair => by
      rcases List.mem_singleton.1 hs with rfl
      exact (sol78ConclAt_fi23 h.mult23 h.lemma63 h.lemma65
        (fi23TwoSylow_of h.lemma25 h.rank23 h.hypOne23) (h.balance23 H hH) (h.claim612E H hH)
        (h.tail23 H hH) N L K t u hN hidx hKP hcov hglob hpair).2.2)
    sol78Closing_fi24in_proved (fi24out_closing h.lemma25 h.rank24 h.hypOne24)
    (fun lit H _ _ ih N L t u hKP hcov hc =>
      fi24_cfg610_false sol78Closing_fi24in_proved h.cfg610 lit ih hKP hcov hc)

theorem FiInputs.given (h : FiInputs) : FiGiven := fiGiven_of h.mult23 h.noStdFi22

end CFSG.EvenSporadicStandard.Induction
