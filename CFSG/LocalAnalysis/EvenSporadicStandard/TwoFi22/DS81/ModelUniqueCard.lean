module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.E0

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem natCard_word : Nat.card (Multiplicative Word) = 2 ^ 23 := by
  rw [Nat.card_congr (Multiplicative.toAdd (α := Word)), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem word_sq (w : Multiplicative Word) : w ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h _

section


theorem natCard_ker_fjHom : Nat.card (fjHom : Multiplicative Word →* J).ker = 2 ^ 12 := by
  rw [← natCard_golayCode]
  refine Nat.card_congr ⟨fun w => ⟨Multiplicative.toAdd w.1, ?_⟩,
    fun w => ⟨Multiplicative.ofAdd w.1, ?_⟩, fun w => Subtype.ext (by simp),
    fun w => Subtype.ext (by simp)⟩
  · refine (fjHom_eq_one_iff _).1 ?_
    rw [ofAdd_toAdd]
    exact MonoidHom.mem_ker.1 w.2
  · exact MonoidHom.mem_ker.2 ((fjHom_eq_one_iff w.1).2 w.2)

theorem fjHom_range_le_Cd : (fjHom : Multiplicative Word →* J).range ≤ Cd := by
  rintro _ ⟨w, rfl⟩
  exact fjHom_mem_Cd w

theorem E0_card : Nat.card E0 = 2 ^ 11 := by
  have h := Subgroup.card_ker_mul_card_range (fjHom : Multiplicative Word →* J)
  rw [natCard_ker_fjHom, natCard_word] at h
  have h11 : Nat.card (fjHom : Multiplicative Word →* J).range = 2 ^ 11 := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ 12 by norm_num) ?_
    rw [h]
    norm_num
  rw [← h11]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe fjHom_range_le_Cd).toEquiv

theorem E0_sq : ∀ e ∈ E0, e ^ 2 = 1 := by
  intro e he
  obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 he
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hw, ← map_pow, word_sq, map_one]
  rfl

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81
