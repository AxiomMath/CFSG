module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionOuter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddBasic

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open F4Pilot (normalizerMulAut)

set_option linter.unusedSectionVars false


section Aut

variable {K : Type} [Field K] [Finite K]

theorem e7_entrywise_complement {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsCyclic (entrywiseAdjointAutHom (τ := .E7) (K := K)).range ∧
      (∀ β ∈ (entrywiseAdjointAutHom (τ := .E7) (K := K)).range,
        β ∈ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range → β = 1) ∧
      ∀ α : MulAut (adjointGroup .E7 K), ∃ g : adjointGroup .E7 K,
        ∃ β ∈ (entrywiseAdjointAutHom (τ := .E7) (K := K)).range, α = MulAut.conj g * β := by
  obtain ⟨hNF, Θ, hΘ, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK .E7 (Or.inl rfl)
  have hcyc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    hK).2
  have hΘσ : ∀ σ : K ≃+* K, Θ (entrywiseAdjointAut .E7 σ) = σ := fun σ =>
    hΘ _ 1 σ fun h => by rw [coe_entrywiseAdjointAut, Subgroup.coe_one, one_mul, inv_one, mul_one]
  refine ⟨isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _), ?_, fun α => ?_⟩
  · rintro _ ⟨σ, rfl⟩ hinn
    have h1 : Θ (entrywiseAdjointAut .E7 σ) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hinn
    rw [hΘσ] at h1
    change entrywiseAdjointAut .E7 σ = 1
    rw [h1, entrywiseAdjointAut_one]
  · obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
    refine ⟨g, entrywiseAdjointAut .E7 σ, ⟨σ, rfl⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
    exact hgσ h

omit [Finite K] in
theorem exists_conj_mem_range_entrywise_of_outer_E7
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {α : MulAut (adjointGroup .E7 K)}
    (hα2 : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range) :
    ∃ φ : MulAut (adjointGroup .E7 K),
      φ * α * φ⁻¹ ∈ (entrywiseAdjointAutHom (τ := .E7) (K := K)).range := by
  obtain ⟨-, Θ, -, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK .E7 (Or.inl rfl)
  have hΘ1 : Θ α ≠ 1 := fun h1 => hαo (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨⟨m, hm⟩, hσc⟩ := (hinv α hα2).resolve_left hΘ1
  have he : 1 ≤ m := by omega
  have hK' : Nat.card K = 2 ^ (2 * m) := by rw [hK, hm, two_mul]
  have hσ : ∀ c, Θ α c = c ^ 2 ^ m := fun c => by rw [hσc, show n / 2 = m by omega]
  obtain ⟨ψ, hψ⟩ :=
    E8Pilot.exists_conj_eq_entrywise_of_outer_E7_E8 (Or.inl rfl) he K hK' (Θ α) hσ hα2 hαo
  exact ⟨ψ, ⟨Θ α, hψ.symm⟩⟩

end Aut

section Ambient


variable {G : Type*} [Group G] [Finite G] {G₀ : Subgroup G}

theorem exists_normal_index_two_of_E7_odd (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ n) (e : G₀ ≃* adjointGroup .E7 K)
    {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  obtain ⟨hcyc, hCInn, hNF⟩ := e7_entrywise_complement hn hK
  have hker : Odd (Nat.card (normalizerMulAut e).ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  have hout := EPilot.normalizerMulAut_not_mem_range_of_odd hZ e htN ht2 htG
  exact EPilot.exists_normal_index_two_of_action_complement_of_isConj (normalizerMulAut e) hker
    (C := (entrywiseAdjointAutHom (τ := .E7) (K := K)).range) hCInn hNF
    (EPilot.exists_normalizerMulAut_eq_conj e) htN ht hout huniq
    (exists_conj_mem_range_entrywise_of_outer_E7 hn hK (EPilot.action_sq_eq_one _ htN ht2) hout)

theorem false_of_simple_of_E7_odd [IsSimpleGroup G]
    (hZ : Odd (Nat.card (centralizer (G₀ : Set G)))) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ n) (e : G₀ ≃* adjointGroup .E7 K) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False :=
  CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG)
    (exists_normal_index_two_of_E7_odd hZ hK e htN ht htG huniq)

end Ambient

end CFSG.SeitzReduction.E7Pilot
