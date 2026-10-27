module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Gen

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem eData_of_parts' {E : Type} [Group E] [IsSimpleGroup E] {n : ℕ} (hn : Nat.card E = n)
    (hnp : ¬ n.Prime) (hbig : 256 < n)
    (hrank : ∃ m : ℕ, (∃ S₀ : Subgroup E, (∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) ∧
        (∀ a ∈ S₀, a * a = 1) ∧ Nat.card S₀ = 2 ^ m) ∧
      ((∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * Nat.card E ∣ gl12 → r ≤ m) ∨
        ((∃ S₈ : Subgroup E, (∀ a ∈ S₈, ∀ b ∈ S₈, a * b = b * a) ∧ (∀ a ∈ S₈, a * a = 1) ∧
            Nat.card S₈ = 8 ∧
            ∀ s ∈ S₈, ∀ t ∈ S₈, s ≠ 1 → t ≠ 1 → ∃ g : E, g * s * g⁻¹ = t) ∧
          ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * Nat.card E ∣ gl12 → r ≤ 6)))
    (hopf : Nat.card (griessHopfMultiplier E) ∣ 2) (houter : Group.IsSolvable (Outer E))
    (h3A6 : ∀ T : Subgroup E, commutator T = ⊤ → Nat.card T = 1080 → ∀ w ∈ T, orderOf w = 3 →
      (∀ t ∈ T, t * w = w * t) → False) :
    EData E := by
  have hnc : ∃ a b : E, a * b ≠ b * a := exists_noncomm_of_not_prime_card (hn ▸ hnp)
  exact
    { chief := ⟨fun N _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N,
        center_eq_one_of_simple hnc, hrank⟩
      hopf := hopf
      outer := houter
      nonab := hnc
      big := hn ▸ hbig
      no3A6 := h3A6 }

end CFSG.EvenSporadicStandard.M24Std
