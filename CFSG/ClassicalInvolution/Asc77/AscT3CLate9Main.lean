module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C20_9Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → 8 < Nat.card R →
        (∀ u ∈ (S : Subgroup G), u * u ∈ sec20X (CoreAssembly.conjClass K) z K K' →
          u ∈ Subgroup.normalizer (K : Set G)) →
        (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
          x * x ∈ sec20X (CoreAssembly.conjClass K) z K K' →
          y * y ∈ sec20X (CoreAssembly.conjClass K) z K K' →
          ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' →
            x ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
            y ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
            x * y ∈ sec20X (CoreAssembly.conjClass K) z K K') ∧
        (∃ a ∈ (S : Subgroup G), InducesFAut K R a ∧ InducesFAut K' R' a)

variable {p f}

theorem c20_9_of_rest (h : C20_9Rest p f) : C20_9 p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 h8
  have h3 := d.late_nine_three c3 h8
  obtain ⟨hrank, ha⟩ := h G K K' J S R R' W V z t d c3 c4 c5 c7 c8 h8 h3
  exact ⟨⟨d.late_not_le_X c3 h8, hrank⟩, ha, h3⟩

end CFSG.ClassicalInvolution.Asc77.T3CII
