module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedDiag
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransfer

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot

section Structure

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem twistedE6_fieldCoordinate :
    ∃ Θ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* RingAut K,
      (∀ g, Θ (MulAut.conj g) = 1) ∧ (∀ δ, Θ (fieldActor σ δ) = δ) ∧
      (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom), α ^ 2 = 1 →
        α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* _).range →
          Θ α = σ) ∧
      Nat.card (RingAut K) = 2 * f ∧ IsCyclic (RingAut K) ∧ σ ≠ 1 ∧ σ ^ 2 = 1 ∧
      ∀ g, ((fieldActor σ σ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
        ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, -, -, -, hinv⟩, hη, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf K hK
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  rw [hσσ'] at hord
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  have hσ2 : σ ^ 2 = 1 := by
    rw [← pow_orderOf_eq_one σ, hord]
    rfl
  obtain ⟨hcard, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
    Nat.prime_two K
    (show Nat.card K = 2 ^ (f * 2) by rw [hK, ← pow_mul])
  refine ⟨Θ, fun g => ?_, fun δ => ?_, fun α hα2 hαI => ?_, by rw [hcard, mul_comm], hcyc, hσ1,
    hσ2, hη⟩
  · exact hΘ _ g 1 1 (by rw [map_one, fieldActor_one, mul_one, mul_one])
  · exact hΘ _ 1 1 δ (by rw [map_one, map_one, one_mul, one_mul])
  · rcases hinv α hα2 with h | ⟨h, -⟩
    · exact absurd h hαI
    · exact h

include hf hK hσ in
theorem twistedE6_fieldActor_complement (hfe : Even f) :
    IsCyclic (fieldActorHom (t := TwistTag.E6) σ).range ∧
    (∀ β ∈ (fieldActorHom (t := TwistTag.E6) σ).range,
      β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* _).range → β = 1) ∧
    ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ∃ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        ∃ β ∈ (fieldActorHom (t := TwistTag.E6) σ).range, α = MulAut.conj g * β := by
  obtain ⟨Θ, hΘI, hΘF, -, -, hcyc, -⟩ := twistedE6_fieldCoordinate hf K hK σ hσ
  have hq : 2 ^ f % 3 = 1 := by
    obtain ⟨k, rfl⟩ := hfe
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  refine ⟨isCyclic_of_surjective _ (fieldActorHom σ).rangeRestrict_surjective, ?_, fun α => ?_⟩
  · rintro β ⟨δ, rfl⟩ ⟨g, hg⟩
    have h1 : δ = 1 := by
      rw [← hΘF δ, ← fieldActorHom_apply, ← hg, hΘI]
    rw [h1, map_one]
  · obtain ⟨g, δ, rfl⟩ := twistedE6_exists_eq_conj_mul_fieldActor Nat.prime_two hf hq hK σ hσ α
    exact ⟨g, fieldActorHom σ δ, ⟨δ, rfl⟩, rfl⟩

end Structure

variable {G : Type*} [Group G] [Finite G] {G₀ : Subgroup G}

end CFSG.SeitzReduction.EPilot
