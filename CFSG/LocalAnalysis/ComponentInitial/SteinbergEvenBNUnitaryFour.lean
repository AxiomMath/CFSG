module

public import CFSG.Blueprint.EvenBNRankTwoExact
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.LocalAnalysis.ComponentInitial.EvenResidual

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Recognition.Exact

variable {G : Type} [Group G]

theorem standardComponentOddCore_eq_bot_of_simple [Finite G] [IsSimpleGroup G]
    (heven : Even (Nat.card G)) : standardComponentOddCore G = ⊥ := by
  refine le_antisymm (sSup_le fun N hN => ?_) bot_le
  have := hN.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h ▸ le_rfl
  · exfalso
    have h1 := hN.2
    rw [h, Subgroup.card_top] at h1
    exact (Nat.not_even_iff_odd.2 h1) heven

theorem isPerfect_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Group.IsPerfect G := by
  refine Group.isPerfect_def.2 ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hab (mem_centralizer_iff.1 (h (mem_top b)) a (mem_top a))
  · exact h

end CFSG.LocalAnalysis.ComponentInitial.EvenResidual
