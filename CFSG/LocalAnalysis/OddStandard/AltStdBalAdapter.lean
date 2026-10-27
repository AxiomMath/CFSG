module

public import CFSG.LocalAnalysis.OddStandard.RouteWBalanced
public import CFSG.LocalAnalysis.OddStandard.AltStdBalDefs

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup

theorem altStdCyclicBalancedFalse_of_order2_big (h2 : AltStdBalancedOrder2)
    (hB : AltStdBalancedBig) : AltStdCyclicBalancedFalse := by
  intro G _ _ L hS n hn hθ S hcyc hz
  have heven : Even (Nat.card (centralizer (L : Set G))) := hS.standard.2.1
  rcases card_eq_two_or_four_le heven S with h | h
  · exact h2 G L hS n hn hθ S hcyc h hz
  · exact hB G L hS n hn hθ S hcyc h hz

@[expose] def AltStdBalancedOrder2Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
          (∀ z : G, z ∈ centralizer (L : Set G) → orderOf z = 2 →
            centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) → False

@[expose] def AltStdBalancedOrder2Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
          (∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 ∧
            ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) → False

theorem altStdBalancedOrder2_of_inner_outer (hI : AltStdBalancedOrder2Inner)
    (hO : AltStdBalancedOrder2Outer) : AltStdBalancedOrder2 := by
  intro G _ _ L hS n hn hθ S hcyc h2 hbal
  by_cases hex : ∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 ∧
      ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)
  · exact hO G L hS n hn hθ S hcyc h2 hbal hex
  · push Not at hex
    exact hI G L hS n hn hθ S hcyc h2 hbal hex

end CFSG.OddStandard.AltStdBal
