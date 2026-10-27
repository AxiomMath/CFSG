module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6KillSquare
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassList

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem twistedE6KillPair [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) {δ : K}
    (hδ : δ + σ δ = 1) : TwistedE6KillPair K σ :=
  twistedE6KillPair_of_square hσσ fun _ _ _ hJ hi _ hc => twKill_square_step hσσ hδ hJ hi hc

theorem twistedE6Kill {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : TwistedE6Kill K σ.toRingHom := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have hσσ : ∀ y : K, σ.toRingHom (σ.toRingHom y) = y := fun y => by
    have h := congrArg (fun g : K ≃+* K => g y) (twistedE6_sigma_pow_order hK hσ)
    simpa [TwistTag.order, pow_two] using h
  obtain ⟨δ, hδ⟩ := exists_twistedE6_add_sigma_eq_one hf hK hσ
  exact ⟨twistedE6KillFixed hσσ, twistedE6KillPair hσσ hδ⟩

end CFSG.SeitzReduction
