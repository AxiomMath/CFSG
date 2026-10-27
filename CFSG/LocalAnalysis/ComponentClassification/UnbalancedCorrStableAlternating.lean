module

import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup Equiv
open CFSG.ComponentClassification.UnbalancedLayer (GSUnbalancingTriple)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

theorem assembly_isStandardSubgroup_of_isStandardSubgroup {Y : Type*} [Group Y]
    {L : Subgroup Y} (h : IsStandardSubgroup L) :
    Assembly.ComponentType.IsStandardSubgroup L :=
  StandardSubgroupAPI.isStandardSubgroup_iff_assembly.1 h

theorem five_le_of_mulEquiv_alternatingGroup {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : ∃ u v : Y, u * v ≠ v * u) {n : ℕ} (φ : Y ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  by_contra h
  push Not at h
  obtain ⟨u, v, huv⟩ := hY
  rcases (show n ≤ 3 ∨ n = 4 by omega) with h3 | h4
  · have hc := alternatingGroup.isMulCommutative_of_card_le_three (α := Fin n) (by simpa using h3)
    apply huv
    apply φ.injective
    rw [map_mul, map_mul]
    exact hc.is_comm.comm _ _
  · subst h4
    have hs : IsSimpleGroup (alternatingGroup (Fin 4)) := φ.symm.isSimpleGroup
    have h4 : Nat.card (Fin 4) = 4 := by simp
    have hn := alternatingGroup.normal_kleinFour h4
    have hcard := alternatingGroup.kleinFour_card_of_card_eq_four h4
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup.kleinFour (Fin 4)) with
      h | h
    · rw [h, Subgroup.card_bot] at hcard
      exact absurd hcard (by norm_num)
    · rw [h, Subgroup.card_top, nat_card_alternatingGroup, h4] at hcard
      exact absurd hcard (by decide)

variable {G : Type} [Group G] [Finite G]

end CFSG.ComponentClassification.UnbalancedCorr
