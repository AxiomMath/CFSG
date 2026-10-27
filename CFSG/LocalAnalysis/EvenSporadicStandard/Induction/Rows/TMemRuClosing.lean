module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuLocal39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuConfig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma36Q
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuInputsHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem sol78SettingLocalQ_ru_proved (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru) :
    Sol78SettingLocalQ .Ru RuQ RuPair := by
  intro H _ _ L K u hcov hQ
  exact ⟨solomonLocalQ_ru hf (hcov.isSporadic_of_mult hmult) hQ.1, hQ.1⟩

theorem solomonCorePAt_ru (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru)
    {H : Type} [Group H] [Finite H] (hbal : RuBalanceAt H) :
    SolomonCorePAt .Ru RuQ H := by
  intro N L K t u hcov hhyp hQ
  have hL := hcov.isSporadic_of_mult hmult
  have ht2 := hhyp.t_order
  have htL := hhyp.t_mem
  have hperf : _root_.commutator ↥L = ⊤ := Group.isPerfect_def.1 hcov.isQuasisimple.1
  have hLN : L ≤ N :=
    le_of_perfect_of_index_le_four hhyp.fstar.normal (by have := hhyp.index_le_two; omega) hperf
  have hLle : L ≤ centralizer ({t} : Set H) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL l hl)
  have hcomp : IsCompIn L (centralizer ({t} : Set H)) :=
    isCompIn_of_normal hLle hcov.isQuasisimple
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).2
        (hhyp.standardL.centralizer_le_normalizer htL ht2))
  have hbalt := hbal N hhyp.fstar hhyp.index_le_two hhyp.kProper L t ht2 hcomp hcov hQ.2.1
  have htN : t ∈ N := hQ.2.2 N t hhyp
  exact ru_false_of_fStar hf hhyp.fstar.isSimpleGroup hhyp.fstar.nonabelian hLN htN hL hQ.1 ht2
    htL hbalt (mem_of_hyp35 hhyp.hyp35)

theorem solomonCorePHered_ru (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru)
    (hbal : RuBalanceHered) : SolomonCorePHered .Ru RuQ :=
  fun H _ _ hH => solomonCorePAt_ru hf hmult (hbal H hH)

theorem sol78ClosingHered_ru_proved (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru)
    (hbal : RuBalanceHered) : Sol78ClosingHered [.Ru] (fun _ => RuQ) :=
  sol78ClosingHered_of_partsP (S := [.Ru]) (Q := fun _ => RuQ) (P := fun _ => RuPair)
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact sol78SettingLocalQ_ru_proved hf hmult)
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact sol78Local39Q_ru hf hmult)
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact solomonCorePHered_ru hf hmult hbal)

end CFSG.EvenSporadicStandard.Induction
