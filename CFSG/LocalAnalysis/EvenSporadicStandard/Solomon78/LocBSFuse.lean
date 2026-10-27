module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLocal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

@[expose] def TwoCentralFused (K : Subgroup G) : Prop :=
  ∀ k ∈ K, ∀ k' ∈ K, k * k = 1 → k' * k' = 1 → k ≠ 1 → k' ≠ 1 →
    twoAdic K ≤ twoAdic (K ⊓ centralizer ({k} : Set G)) →
    twoAdic K ≤ twoAdic (K ⊓ centralizer ({k'} : Set G)) → ∃ c ∈ K, c * k * c⁻¹ = k'

@[expose] def OneClassOutside (K : Subgroup G) : Prop :=
  ∀ v ∈ K, ∀ v' ∈ K, v * v = 1 → v' * v' = 1 → v ≠ 1 → v' ≠ 1 →
    v ∉ (center K).map K.subtype → v' ∉ (center K).map K.subtype → ∃ c ∈ K, c * v * c⁻¹ = v'

theorem mul_self_eq_one_of_orderOf {x : G} (h : orderOf x = 2) : x * x = 1 := by
  have : x ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one x
  rwa [pow_two] at this

theorem ne_one_of_orderOf {x : G} (h : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  exact absurd h (by decide)

theorem orderOf_eq_two_of_mul_self {x : G} (h : x * x = 1) (h1 : x ≠ 1) :
    orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) h1

theorem mem_sup_zpowers_cases {K : Subgroup G} {u : G} (hu2 : orderOf u = 2)
    (hKu : ∀ k ∈ K, k * u = u * k) {x : G} (hx : x ∈ K ⊔ zpowers u) :
    ∃ k ∈ K, ∃ ε : G, (ε = 1 ∨ ε = u) ∧ x = k * ε := by
  obtain ⟨k, hk, n, rfl⟩ := exists_mul_zpow_of_mem_sup hKu hx
  have h : u ^ (n % 2) = u ^ n := by simpa [hu2] using zpow_mod_orderOf u n
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · refine ⟨k, hk, 1, Or.inl rfl, ?_⟩
    rw [← h, h0]
    simp
  · refine ⟨k, hk, u, Or.inr rfl, ?_⟩
    rw [← h, h1]
    simp

theorem map_conj_eq_of_mem {K : Subgroup G} {c : G} (hc : c ∈ K) : K.map (conjHom c) = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.mul_mem (K.mul_mem hc hy) (K.inv_mem hc)
  · intro hx
    refine ⟨c⁻¹ * x * c, K.mul_mem (K.mul_mem (K.inv_mem hc) hx) hc, ?_⟩
    show c * (c⁻¹ * x * c) * c⁻¹ = x
    group

theorem map_conj_eq_of_mem' {L : Subgroup G} {c : G} (hc : c ∈ L) : L.map (conjHom c) = L :=
  map_conj_eq_of_mem hc

theorem eps_facts {u g : G} (hu2 : orderOf u = 2) (hug : g * u * g⁻¹ = u) {ε : G}
    (hε : ε = 1 ∨ ε = u) : ε * ε = 1 ∧ g * ε * g⁻¹ = ε := by
  have huu := mul_self_eq_one_of_orderOf hu2
  rcases hε with rfl | rfl
  · simp
  · exact ⟨huu, hug⟩

variable [Finite G]

end CFSG.EvenSporadicStandard.Solomon78
