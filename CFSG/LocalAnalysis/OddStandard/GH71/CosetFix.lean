module

public import CFSG.LocalAnalysis.OddStandard.GH71.Basic

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_centralized_in_coset {A K N₀ : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hN₀ : Odd (Nat.card N₀)) (hAN : A ≤ normalizer (N₀ : Set G))
    (htriv : ∀ a ∈ A, ∀ k ∈ K, k⁻¹ * (a * k * a⁻¹) ∈ N₀) {k : G} (hk : k ∈ K) :
    ∃ n ∈ N₀, k * n ∈ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ (a : ↥A) (n : ↥N₀), k⁻¹ * ((a : G) * (k * n) * (a : G)⁻¹) ∈ N₀ := by
    intro a n
    have h1 := htriv a a.2 k hk
    have h2 : (a : G) * n * (a : G)⁻¹ ∈ N₀ := (mem_normalizer_iff.mp (hAN a.2) n).mp n.2
    have e : k⁻¹ * ((a : G) * (k * n) * (a : G)⁻¹) =
        (k⁻¹ * ((a : G) * k * (a : G)⁻¹)) * ((a : G) * n * (a : G)⁻¹) := by group
    rw [e]; exact N₀.mul_mem h1 h2
  let act : MulAction ↥A ↥N₀ :=
    { smul := fun a n => ⟨k⁻¹ * ((a : G) * (k * n) * (a : G)⁻¹), hmem a n⟩
      one_smul := fun n => by
        apply Subtype.ext
        show k⁻¹ * ((1 : G) * (k * n) * (1 : G)⁻¹) = n
        group
      mul_smul := fun a b n => by
        apply Subtype.ext
        show k⁻¹ * (((a : G) * b) * (k * n) * ((a : G) * b)⁻¹) =
          k⁻¹ * ((a : G) * (k * (k⁻¹ * ((b : G) * (k * n) * (b : G)⁻¹))) * (a : G)⁻¹)
        group }
  obtain ⟨n, hn⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card ↥N₀ (not_two_dvd_of_odd hN₀)
  refine ⟨n, n.2, ?_⟩
  rw [mem_centralizer_iff]
  intro a ha
  have h1 := congrArg Subtype.val (hn ⟨a, ha⟩)
  change k⁻¹ * (a * (k * n) * a⁻¹) = n at h1
  have h2 : a * (k * n) * a⁻¹ = k * n := by
    calc a * (k * n) * a⁻¹ = k * (k⁻¹ * (a * (k * n) * a⁻¹)) := by group
      _ = k * n := by rw [h1]
  calc a * (k * n) = a * (k * n) * a⁻¹ * a := by group
    _ = k * n * a := by rw [h2]

end CFSG.OddStandard.GH71
