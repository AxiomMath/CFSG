module

public import CFSG.Blueprint.MultiplierDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResEData

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem range_elemAb_of_injective {A G : Type*} [CommGroup A] [Group G] (ψ : A →* G)
    (hψ : Function.Injective ψ) (h2 : ∀ a : A, a * a = 1) :
    (∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a) ∧ (∀ a ∈ ψ.range, a * a = 1) ∧
      Nat.card ψ.range = Nat.card A := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_mul, h2, map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm

theorem exists_noncomm_of_not_prime_card {E : Type} [Group E] [IsSimpleGroup E]
    (h : ¬ (Nat.card E).Prime) : ∃ a b : E, a * b ≠ b * a := by
  by_contra hne
  have hcomm : ∀ a b : E, a * b = b * a := fun a b =>
    by_contra fun hab => hne ⟨a, b, hab⟩
  let _ : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  exact h IsSimpleGroup.prime_card

theorem center_eq_one_of_simple {E : Type} [Group E] [IsSimpleGroup E]
    (h : ∃ a b : E, a * b ≠ b * a) : ∀ e : E, (∀ x : E, x * e = e * x) → e = 1 := by
  intro e he
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center E) with hbot | htop
  · have : e ∈ center E := Subgroup.mem_center_iff.2 he
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  · obtain ⟨a, b, hab⟩ := h
    have : a ∈ center E := htop ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.1 this b) (Ne.symm hab)

theorem card_generic_prod_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

theorem eData_of_parts {E : Type} [Group E] [IsSimpleGroup E] {n : ℕ} (hn : Nat.card E = n)
    (hnp : ¬ n.Prime) (hbig : 256 < n) (h1080 : ¬ 1080 ∣ n)
    (hrank : ∃ m : ℕ, (∃ S₀ : Subgroup E, (∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) ∧
        (∀ a ∈ S₀, a * a = 1) ∧ Nat.card S₀ = 2 ^ m) ∧
      ((∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * Nat.card E ∣ gl12 → r ≤ m) ∨
        ((∃ S₈ : Subgroup E, (∀ a ∈ S₈, ∀ b ∈ S₈, a * b = b * a) ∧ (∀ a ∈ S₈, a * a = 1) ∧
            Nat.card S₈ = 8 ∧
            ∀ s ∈ S₈, ∀ t ∈ S₈, s ≠ 1 → t ≠ 1 → ∃ g : E, g * s * g⁻¹ = t) ∧
          ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * Nat.card E ∣ gl12 → r ≤ 6)))
    (hopf : Nat.card (griessHopfMultiplier E) ∣ 2) (houter : Group.IsSolvable (Outer E)) :
    EData E := by
  have hnc : ∃ a b : E, a * b ≠ b * a := exists_noncomm_of_not_prime_card (hn ▸ hnp)
  exact
    { chief := ⟨fun N _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N,
        center_eq_one_of_simple hnc, hrank⟩
      hopf := hopf
      outer := houter
      nonab := hnc
      big := hn ▸ hbig
      no3A6 := fun T _ hT _ _ _ _ =>
        h1080 (hn ▸ hT ▸ Subgroup.card_subgroup_dvd_card T) }

end CFSG.EvenSporadicStandard.M24Std
