module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPerfect

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphTwistedDKernelNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Perfect

variable {k : Type} [Field k]

theorem twLevi_Y_eq_sup (θ : k →+* k) :
    twLevi k θ AmalgamNeighbour.Y.nodes = twLevi k θ {0} ⊔ twLevi k θ {1, 2} := by
  refine le_antisymm (iSup₂_le fun j hj => ?_)
    (sup_le (CFSG.LieType.CurtisTits.levi_mono _ zero_subset_Y)
      (CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_Y))
  by_cases hj0 : j = 0
  · subst hj0
    exact le_sup_of_le_left
      (CFSG.LieType.CurtisTits.rankOne_le_levi _ (Finset.mem_singleton_self 0))
  · exact le_sup_of_le_right
      (CFSG.LieType.CurtisTits.rankOne_le_levi _ (mem_one_two_of_mem_nodes_Y hj hj0))

theorem commutator_twLevi_Y (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {t : kˣ} (htθ : θ t = t)
    (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ⁅twLevi k θ AmalgamNeighbour.Y.nodes, twLevi k θ AmalgamNeighbour.Y.nodes⁆ =
      twLevi k θ AmalgamNeighbour.Y.nodes := by
  refine le_antisymm (commutator_le_self _) ?_
  have h0 := commutator_twLevi_zero θ hθ htθ ht
  have h12 := commutator_twLevi_one_two θ hθ htθ ht
  rw [twLevi_Y_eq_sup]
  calc twLevi k θ {0} ⊔ twLevi k θ {1, 2}
      = ⁅twLevi k θ {0}, twLevi k θ {0}⁆ ⊔ ⁅twLevi k θ {1, 2}, twLevi k θ {1, 2}⁆ := by
        rw [h0, h12]
    _ ≤ _ := sup_le (commutator_mono le_sup_left le_sup_left)
        (commutator_mono le_sup_right le_sup_right)

theorem finite_twLevi [Finite k] (θ : k →+* k) (S : Finset (Fin (Tag.rank .F4))) :
    Finite (twLevi k θ S) := by
  have : Finite (Module.End k (Fin CFSG.LieType.Steinberg.Minuscule.e6Data.d →₀ k)) :=
    Module.finite_of_finite k
  infer_instance

end Perfect

end CFSG.SeitzReduction.F4Pilot
