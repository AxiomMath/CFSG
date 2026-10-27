module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeSplit
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListFinal

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]


theorem twistedE6FrameReduction_of_kill_charTwo [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) (hkill : TwistedE6Kill K σ) : TwistedE6FrameReduction K σ := by
  intro ℓ hℓ h2
  obtain ⟨hℓU, hℓΓ⟩ := Subgroup.mem_inf.1 hℓ
  have hall := twistedE6CascadeTree_roots.2.2.2.2.2.2.2.2.2.2.2
  have hℓU' : ℓ ∈ rootSpan TwistTag.E6.tag K
      {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := hℓU
  have hℓ' : ℓ ∈ rootSpan TwistTag.E6.tag K
      (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJE6}) :=
    classDescent_rootSpan_mono (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α})
      (T := parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJE6})
      (fun α hα => ⟨⟨hα.1, fun l hl => absurd (hall l) hl⟩, hα⟩) hℓU'
  obtain ⟨g, -, hgC, R, ⟨hnd, hpos, hpw⟩, c, hc, he⟩ :=
    twistedE6LevelRes_E6 hσσ hkill (twistedE6LevelA3'_holds σ) hℓ' hℓΓ h2
  exact ⟨g, hgC, R, hnd, fun β hβ => ⟨(hpos β hβ).1, (hpos β hβ).2.1⟩, hpw, c, hc, he⟩

theorem twistedE6FrameReduction_of_kill {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hkill : TwistedE6Kill K σ.toRingHom) :
    TwistedE6FrameReduction K σ.toRingHom := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have hσσ : ∀ y : K, σ (σ y) = y := fun y => by
    have h := congrArg (fun g : K ≃+* K => g y) (twistedE6_sigma_pow_order hK hσ)
    simpa [TwistTag.order, pow_two] using h
  exact twistedE6FrameReduction_of_kill_charTwo hσσ hkill


theorem exceptionalHypothesisOne_of_twistedE6Kill
    (hkill : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → TwistedE6Kill K σ.toRingHom) :
    ExceptionalHypothesisOne :=
  exceptionalHypothesisOne_of_twistedE6FrameReduction fun f K _ σ hf hK hσ =>
    twistedE6FrameReduction_of_kill hf hK hσ (hkill f K σ hf hK hσ)

end CFSG.SeitzReduction
