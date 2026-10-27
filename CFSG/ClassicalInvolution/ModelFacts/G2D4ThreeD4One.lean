module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance.Q27

theorem involutionOddCoreTrivial_of_conj {K : Type} [Group K]
    (hconj : ∀ u v : K, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → ∃ g : K, g * u * g⁻¹ = v)
    (h : ∃ u₀ : K, u₀ * u₀ = 1 ∧ u₀ ≠ 1 ∧ ∀ N : Subgroup K,
      N ≤ Subgroup.centralizer ({u₀} : Set K) →
      (∀ c ∈ Subgroup.centralizer ({u₀} : Set K), ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      Odd (Nat.card N) → N = ⊥) :
    InvolutionOddCoreTrivial K := by
  obtain ⟨u₀, hu₀, hu₀1, h₀⟩ := h
  intro u hu hu1 N hNc hNnorm hNodd
  obtain ⟨g, hg⟩ := hconj u₀ u hu₀ hu hu₀1 hu1
  set N' : Subgroup K := conjSub g⁻¹ N with hN'
  have hmemN' : ∀ x, x ∈ N' ↔ g * x * g⁻¹ ∈ N := fun x => by
    rw [hN', mem_conjSub_iff, inv_inv]
  have hcomm_iff : ∀ x : K, x * u₀ = u₀ * x ↔ (g * x * g⁻¹) * u = u * (g * x * g⁻¹) := by
    intro x
    rw [← hg]
    constructor
    · intro h
      calc g * x * g⁻¹ * (g * u₀ * g⁻¹) = g * (x * u₀) * g⁻¹ := by group
        _ = g * (u₀ * x) * g⁻¹ := by rw [h]
        _ = g * u₀ * g⁻¹ * (g * x * g⁻¹) := by group
    · intro h
      have h2 : g * (x * u₀) * g⁻¹ = g * (u₀ * x) * g⁻¹ := by
        calc g * (x * u₀) * g⁻¹ = g * x * g⁻¹ * (g * u₀ * g⁻¹) := by group
          _ = g * u₀ * g⁻¹ * (g * x * g⁻¹) := h
          _ = g * (u₀ * x) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  have hN'c : N' ≤ Subgroup.centralizer ({u₀} : Set K) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm_iff x).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hNc ((hmemN' x).mp hx)))
  have hnorm : ∀ c ∈ Subgroup.centralizer ({u₀} : Set K), ∀ n ∈ N', c * n * c⁻¹ ∈ N' := by
    intro c hc n hn
    rw [hmemN'] at hn ⊢
    have hcu : g * c * g⁻¹ ∈ Subgroup.centralizer ({u} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm_iff c).mp (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have h1 := hNnorm _ hcu _ hn
    have e : g * (c * n * c⁻¹) * g⁻¹ = g * c * g⁻¹ * (g * n * g⁻¹) * (g * c * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact h1
  have hodd' : Odd (Nat.card N') := by
    have : Nat.card N' = Nat.card N :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [this]
    exact hNodd
  have hN'bot : N' = ⊥ := h₀ N' hN'c hnorm hodd'
  rw [Subgroup.eq_bot_iff_forall] at hN'bot ⊢
  intro n hn
  have h1 : g⁻¹ * n * g ∈ N' := (hmemN' _).mpr (by
    have e : g * (g⁻¹ * n * g) * g⁻¹ = n := by group
    rw [e]
    exact hn)
  have h4 : g⁻¹ * n * g = 1 := hN'bot _ h1
  calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
    _ = 1 := by rw [h4]; group

@[expose] def TD4ThreeOddCoreOne : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), StatedLieAdmissible .trialityD4 n p e → p ^ e = 3 →
    ∃ u₀ : (modelUniv .trialityD4 n p e hp).K, u₀ * u₀ = 1 ∧ u₀ ≠ 1 ∧ ∀ N : Subgroup _,
      N ≤ Subgroup.centralizer ({u₀} : Set (modelUniv .trialityD4 n p e hp).K) →
      (∀ c ∈ Subgroup.centralizer ({u₀} : Set (modelUniv .trialityD4 n p e hp).K),
        ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) → N = ⊥

theorem td4ThreeOddCore_of_one (h : TD4ThreeOddCoreOne) : TD4ThreeOddCore := by
  intro n p e hp hadm he3
  have hn : n = 0 := hadm.2.2
  subst hn
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ^ e = 3 := he3
    have : 2 ∣ 3 := h2 ▸ dvd_pow_self 2 (by have := hadm.2.1; omega)
    omega
  exact involutionOddCoreTrivial_of_conj
    (fun u v hu hv hu1 hv1 =>
      CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hadm.2.1
        hu hv hu1 hv1)
    (h 0 p e hp hadm he3)

end CFSG.ClassicalInvolution.G2D4Models
