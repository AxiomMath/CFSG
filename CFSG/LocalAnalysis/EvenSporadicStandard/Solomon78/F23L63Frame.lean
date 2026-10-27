module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelOrbAct
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueCard

public section

namespace CFSG.EvenSporadicStandard.Solomon78.F23L63

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section Frame

@[expose] noncomputable def frameE : Subgroup J := fjHom.range

theorem frameE_le_Cd : frameE ≤ Cd := fjHom_range_le_Cd

theorem frameE_card : Nat.card (frameE : Subgroup J) = 2 ^ 11 := by
  rw [← E0_card, E0]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe frameE_le_Cd).toEquiv).symm

theorem frameE_sq : ∀ x ∈ (frameE : Subgroup J), x ^ 2 = 1 := by
  rintro _ ⟨w, rfl⟩
  rw [← map_pow, word_sq, map_one]

theorem frameE_comm : ∀ x ∈ (frameE : Subgroup J), ∀ y ∈ (frameE : Subgroup J), x * y = y * x := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem fjPt_mem_frameE (i : Fin 23) : fjPt i ∈ (frameE : Subgroup J) :=
  ⟨eVec i, fjHom_eVec i⟩

theorem d_mem_frameE : d ∈ (frameE : Subgroup J) := fjPt_zero ▸ fjPt_mem_frameE 0

end Frame

section Points

theorem mem_frameE_and_D23_iff {x : J} : x ∈ (frameE : Subgroup J) ∧ x ∈ D23 ↔ ∃ i, fjPt i = x := by
  constructor
  · rintro ⟨hxE, hxD⟩
    by_cases hxd : x = d
    · exact ⟨0, by rw [fjPt_zero, hxd]⟩
    · have hxs : x ∈ star := ⟨hxD, hxd, frameE_comm x hxE d d_mem_frameE⟩
      obtain ⟨i, -, hi⟩ := star_mem_range hxs hxE
      exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨fjPt_mem_frameE i, fjPt_mem i⟩

theorem ncard_frameE_D23 : Set.ncard {x : J | x ∈ (frameE : Subgroup J) ∧ x ∈ D23} = 23 := by
  have h : {x : J | x ∈ (frameE : Subgroup J) ∧ x ∈ D23} = Set.range fjPt := by
    ext x
    exact mem_frameE_and_D23_iff
  rw [h, Set.ncard_range_of_injective fjPt_injective, Nat.card_eq_fintype_card, Fintype.card_fin]

end Points

end CFSG.EvenSporadicStandard.Solomon78.F23L63
