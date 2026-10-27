module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {U : Submodule (ZMod 2) V}

theorem exists_strictMin_offender [Finite G] (hb : IsBestOffenderOn ρ A U)
    (hne : ¬ A ≤ cenOn ρ A U) :
    ∃ B : Subgroup G, B ≤ A ∧ cenOn ρ A U ≤ B ∧ ¬ B ≤ cenOn ρ A U ∧
      Nat.card B * Nat.card (fixOn ρ B U) = Nat.card A * Nat.card (fixOn ρ A U) ∧
      IsBestOffenderOn ρ B U ∧ cenOn ρ B U = cenOn ρ A U ∧
      ∀ B' : Subgroup G, cenOn ρ A U ≤ B' → B' < B → ¬ B' ≤ cenOn ρ A U →
        Nat.card B' * Nat.card (fixOn ρ B' U) < Nat.card A * Nat.card (fixOn ρ A U) := by
  classical
  set C := cenOn ρ A U with hC
  let S : Set (Subgroup G) :=
    {B | B ≤ A ∧ C ≤ B ∧ ¬ B ≤ C ∧
      Nat.card B * Nat.card (fixOn ρ B U) = Nat.card A * Nat.card (fixOn ρ A U)}
  have hS : S.Nonempty := ⟨A, le_rfl, cenOn_le ρ A U, hne, rfl⟩
  obtain ⟨B, hBS, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min S hS
  obtain ⟨hBA, hCB, hBC, hBw⟩ := hBS
  refine ⟨B, hBA, hCB, hBC, hBw, ⟨hb.1.mono_left hBA, fun B' hB' => ?_⟩, ?_, ?_⟩
  · rw [hBw]
    exact hb.2 B' (hB'.trans hBA)
  · apply le_antisymm
    · intro g hg
      exact ⟨hBA hg.1, hg.2⟩
    · intro g hg
      exact ⟨hCB hg, hg.2⟩
  · intro B' hCB' hB'B hB'C
    have hle : Nat.card B' * Nat.card (fixOn ρ B' U) ≤ Nat.card A * Nat.card (fixOn ρ A U) :=
      hb.2 B' (hB'B.le.trans hBA)
    refine lt_of_le_of_ne hle fun heq => ?_
    exact hmin B' ⟨hB'B.le.trans hBA, hCB', hB'C, heq⟩ hB'B

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
