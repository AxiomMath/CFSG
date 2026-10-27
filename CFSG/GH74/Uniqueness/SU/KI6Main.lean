module

public import CFSG.GH74.Uniqueness.SU.KI6Simple

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Uniqueness.SU.K.R3

@[expose] def KI6A : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H), Cfg H T H₀ →
    ∀ L : Subgroup H, IsComponent L → 2 ≤ Open.pRank 2 L → ¬ IsSimpleGroup ↥L →
      ((L = ⊤ ∧ IsTwoAlt ↥L 9 ∧ IsTwoAlt ↥H₀ 8) ∨
        (IsTwoSz8 ↥L ∧ L ⊔ centralizer (L : Set H) = ⊤ ∧
          Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ L)) ∧
      IsCyclic ↥(center ↥(T : Subgroup H))

@[expose] def KI6B : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H), Cfg H T H₀ →
    (∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) → Concl H T H₀

theorem ki6_iff : KI6 ↔ ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H),
    Cfg H T H₀ → Concl H T H₀ :=
  ⟨fun h H _ _ T H₀ c => h H c.gh c.odd c.rank c.cen T H₀ c.gamma c.ne,
   fun h H _ _ gh odd rank cen T H₀ gamma ne => h H T H₀ ⟨gh, odd, rank, cen, gamma, ne⟩⟩

theorem ki6_of_residuals
    (hA : KI6A) (hB : KI6B) (h34 : Bender34c) : KI6 := by
  rw [ki6_iff]
  intro H _ _ T H₀ h
  by_cases hs : ∃ L : Subgroup H, IsComponent L ∧ IsSimpleGroup ↥L
  · obtain ⟨L, hL, hLs⟩ := hs
    exact ki6_simple h34 h hL hLs
  · push Not at hs
    by_cases hr : ∃ L : Subgroup H, IsComponent L ∧ 2 ≤ Open.pRank 2 L
    · obtain ⟨L, hL, hrank⟩ := hr
      obtain ⟨-, hLnotle, -, hrk, -⟩ := h.rank2_component hL hrank
      obtain ⟨hcd, hcyc⟩ := hA H T H₀ h L hL hrank (hs L hL)
      refine ⟨L, hL, hLnotle, hrk, ⟨?_, Or.inr hcyc⟩⟩
      rcases hcd with hc | hd
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hd))
    · push Not at hr
      exact hB H T H₀ h (fun L hL => by have := hr L hL; omega)

end CFSG.GH74.Uniqueness.SU.K.R6
