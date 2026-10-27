module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionCore
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionInner

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner)

@[expose] def OuterTwoPartBoundE6 (K : Type) [Field K]
    (f : ℕ) : Prop :=
  ∀ β : MulAut (adjointGroup .E6 K), orderOf β = 2 → β ∉ OuterAutomorphisms.inner _ →
    ¬ 2 ^ (26 * f) ∣ Nat.card (centralizer ({β} : Set (MulAut (adjointGroup .E6 K))))


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem forall_inner_E6_of_outer (hset : StandardSetting G L) {f : ℕ} (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hB : OuterTwoPartBoundE6 K f) :
    ∀ g : G, g⁻¹ * t * g ≠ t → g⁻¹ * t * g ∈ L ⊔ zpowers t →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  exact forall_inner_of_two_pow_dvd hset e (center_adjointGroup_eq_bot_field _ K) ht hKt (26 * f)
    (fun w hw => two_pow_dvd_card_centralizer_E6 hK hw) hB

end CFSG.SeitzReduction.E6Pilot
