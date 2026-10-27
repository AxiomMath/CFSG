module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorInputs
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLLeviConnected
import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

theorem gomiLeviFactorsSL_of_isChevTwo
    (h : ∀ (G : Type) [Group G] (k f : ℕ), StatedClassicalModel G .PSL k 2 f → IsChevTwo G) :
    GomiLeviFactorsSL := by
  intro m F _ _ _ C hC h2C _
  obtain ⟨e⟩ := nonempty_mulEquiv_leviM_of_isNodeConnected (F := F) hC
  refine GomiLeviFactor.of_mulEquiv e.symm ?_
  left
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  have hadm : StatedLieAdmissible .PSL (C.ncard + 1) 2 f := by
    refine ⟨Nat.prime_two, hf1, by omega, ?_, ?_⟩
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
  have hmodel := CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient
    (m := C.ncard) (F := F) hadm hfcard
  refine IsGomiChevTwo.of_isQuasisimple ?_ ?_ ?_
  ·
    exact CFSG.LieType.Universal.SpecialLinear.isQuasisimple (m := C.ncard) (F := F) h2C
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      CFSG.ClassicalInvolution.ModelFacts.LinearAut.not_dvd_card_center_specialLinearGroup)
  ·
    exact h _ (C.ncard + 1) f hmodel

end CFSG.GroupTheory
