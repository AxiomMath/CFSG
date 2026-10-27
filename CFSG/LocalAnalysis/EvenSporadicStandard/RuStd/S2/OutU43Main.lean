module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Order
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.LieType.Multipliers.U43Bridge

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Multipliers.U43 (F9 card_X₀)

private theorem isSimpleGroup_u43 : IsSimpleGroup U43 := by
  have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F9 3 1
    (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num) 4 (by norm_num) (by simp)
  rwa [pow_one] at h

theorem center_u43_eq_bot : Subgroup.center U43 = ⊥ := by
  have hs := isSimpleGroup_u43
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U43) with h | h
  · exact h
  · have hc : IsMulCommutative U43 := Subgroup.center_eq_top_iff.1 h
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [card_X₀] at hp
    norm_num at hp

theorem conj_injective_u43 : Function.Injective (MulAut.conj : U43 →* MulAut U43) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center U43 := Subgroup.mem_center_iff.2 fun y => by
    have := congrArg (fun σ : MulAut U43 => σ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = (g * y * g⁻¹) * g := by rw [this]
      _ = g * y := by group
  rwa [center_u43_eq_bot, Subgroup.mem_bot] at hmem

theorem card_inner_u43 : Nat.card (inner U43) = Nat.card U43 :=
  (Nat.card_congr (MonoidHom.ofInjective conj_injective_u43).toEquiv).symm

theorem card_mulAut_u43 : Nat.card (MulAut U43) = 8 * Nat.card U43 := by
  have h := (inner U43).card_mul_index
  rw [Subgroup.index_eq_card, card_inner_u43] at h
  have h8 : Nat.card (MulAut U43 ⧸ inner U43) = 8 := card_outer_u43
  rw [← h, h8, mul_comm]

end CFSG.EvenSporadicStandard.RuStd.S2
