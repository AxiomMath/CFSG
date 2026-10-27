module

public import CFSG.HardMathSupport.Foote.Coordinator.Shared
public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSL
public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSU
public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSp
public import CFSG.HardMathSupport.Foote.ModuleExclusions.POmegaOdd
public import CFSG.HardMathSupport.Foote.ModuleExclusions.POmegaPlus
public import CFSG.HardMathSupport.Foote.ModuleExclusions.POmegaMinus
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.Quasithin.EmptyFaithful.S146zYFBL2

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG CFSG.HardMathSupport.Foote.Coordinator CFSG.HardMathSupport.Foote.ModuleExclusions


theorem griessAllModelsStatement : CFSG.Open.GriessAllModelsStatement :=
  fun _ _ t n p f hmodel =>
    CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two.griess_all_models_of_twistedE6_two
      CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.twistedE6TwoMultiplier t n p f hmodel

theorem classicalFiveTarget : ClassicalFiveTarget := by
  intro Q _ t n f hm hnp
  have hGA := griessAllModelsStatement
  have hm' := hm
  obtain ⟨hadm, -⟩ := hm
  cases t
  case PSL =>
    by_cases h : 4 ≤ n ∨ 2 ≤ f
    · exact end415K_of_coverInv (coverInv_psl hGA Q hm' h)
    · have hf : 1 ≤ f := hadm.2.1
      have hn2 : 2 ≤ n := hadm.2.2.1
      have hf1 : f = 1 := by omega
      have hn3 : n ≤ 3 := by omega
      subst hf1
      by_cases hn : n = 3
      · exact (hnp (Or.inl ⟨rfl, hn, rfl⟩)).elim
      · have hn2' : n = 2 := by omega
        subst hn2'
        refine end415K_of_not_dvd ?_
        rw [CFSG.Quasithin.S146zY.card_of_statedPSL_five_one hm']
        norm_num
  case PSU => exact end415K_of_coverInv (coverInv_psu_all hGA Q hm')
  case PSp => exact end415K_of_coverInv (coverInv_psp hGA Q hm')
  case POmegaOdd => exact end415K_of_coverInv (coverInv_pomegaOdd hGA Q hm')
  case POmegaPlus => exact end415K_of_coverInv (coverInv_pomegaPlus hGA Q hm')
  case POmegaMinus => exact end415K_of_coverInv (coverInv_pomegaMinus hGA Q hm')
  all_goals exact hm'.2.elim

end CFSG.HardMathSupport.Foote.FamilyReduction
