module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot

variable {G : Type*} [Group G] [Finite G]

section Action

variable
  {M : Subgroup G} {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem exists_normal_index_two_of_twistedE6_action_of_even (hfe : Even f)
    [Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)]
    (ρ : M →* MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hker : Odd (Nat.card ρ.ker))
    (hInn : ∀ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, ∃ m : M, ρ m = MulAut.conj g)
    {t : G} (htM : t ∈ M) (ht : orderOf t = 2)
    (hout : ρ ⟨t, htM⟩ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* _).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, hη0⟩ := twistedE6_fieldCoordinate hf K hK σ hσ
  obtain ⟨ht1, η, hη, -, -, hnoninner, -, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ.toRingHom hσ
  have hηF : η = fieldActor σ σ := MulEquiv.ext fun h => Subtype.ext ((hη h).trans (hη0 h).symm)
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hτ2 : ρ ⟨t, htM⟩ ^ 2 = 1 := action_sq_eq_one _ htM ht2
  have hout' : ∀ c, ρ ⟨t, htM⟩ ≠ MulAut.conj c := fun c h => hout ⟨c, h.symm⟩
  rcases hnoninner _ hτ2 hout' with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  ·
    rw [hηF] at hφ
    obtain ⟨hFcyc, hFInn, hNF⟩ := twistedE6_fieldActor_complement hf K hK σ hσ hfe
    exact exists_normal_index_two_of_action_complement_of_isConj ρ hker hFInn hNF hInn htM ht
      hout huniq ⟨φ, by rw [hφ]; exact ⟨σ, rfl⟩⟩
  ·
    rw [hηF] at hφ
    obtain ⟨γ, hCInn, hNF, ht1', hγf⟩ := twistedE6_xi_complement hf K hK σ hσ hfe
    refine exists_normal_index_two_of_action_complement_of_isConj ρ hker (C := zpowers γ) hCInn
      hNF hInn htM ht hout huniq ⟨φ, ?_⟩
    rw [hφ, show (⟨_, ht1⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⟨_, ht1'⟩ from rfl,
      ← hγf]
    exact npow_mem_zpowers γ f

include hf hK hσ in
theorem exists_normal_index_two_of_twistedE6_action_of_odd (hfo : Odd f)
    (ρ : M →* MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) {t : G} (htM : t ∈ M)
    (ht : orderOf t = 2)
    (hout : ρ ⟨t, htM⟩ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* _).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  obtain ⟨Θ, -, -, hΘinv, hcard, -, hσ1, -⟩ := twistedE6_fieldCoordinate hf K hK σ hσ
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  refine exists_normal_index_two_of_unique_of_not_four_dvd htM ht huniq (Θ.comp ρ) ?_ ?_
  · rw [hcard]
    obtain ⟨k, rfl⟩ := hfo
    omega
  · rw [MonoidHom.comp_apply, hΘinv _ (action_sq_eq_one _ htM ht2) hout]
    exact hσ1

include hf hK hσ in
theorem exists_normal_index_two_of_twistedE6_action
    [Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)]
    (ρ : M →* MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hker : Odd (Nat.card ρ.ker))
    (hInn : ∀ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, ∃ m : M, ρ m = MulAut.conj g)
    {t : G} (htM : t ∈ M) (ht : orderOf t = 2)
    (hout : ρ ⟨t, htM⟩ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* _).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  rcases Nat.even_or_odd f with hfe | hfo
  · exact exists_normal_index_two_of_twistedE6_action_of_even hf K hK σ hσ hfe ρ hker hInn htM ht
      hout huniq
  · exact exists_normal_index_two_of_twistedE6_action_of_odd hf K hK σ hσ hfo ρ htM ht hout huniq

end Action

variable {G₀ : Subgroup G}

end CFSG.SeitzReduction.EPilot
