module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusData

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup

theorem odd_natCard_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, Odd (orderOf g)) : Odd (Nat.card G) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := h g
  rw [hg] at this
  exact (Nat.not_even_iff_odd.mpr this) even_two

theorem isTorusDataIn_of_hom {G A : Type} [Group G] [Finite G] [CommGroup A] {c : ℕ}
    (τ : A →* G) (hτ : Function.Injective τ) {N : ℕ} (hN : Odd N) (hAN : ∀ a : A, a ^ N = 1)
    (Ai : Fin c → Subgroup A) (hAsup : ∀ i j, i ≠ j → Ai i ⊔ Ai j = ⊤)
    (P : G) (π : Equiv.Perm (Fin c)) (hπ : ∀ i j : Fin c, ∃ k : ℕ, (π ^ k) i = j)
    (hconjT : ∀ a : A, ∃ a' : A, P * τ a * P⁻¹ = τ a')
    (hconjT' : ∀ a : A, ∃ a' : A, P⁻¹ * τ a * P = τ a')
    (hconj : ∀ i, ∀ a ∈ Ai i, ∃ a' ∈ Ai (π i), P * τ a * P⁻¹ = τ a')
    (hconj' : ∀ i, ∀ a ∈ Ai (π i), ∃ a' ∈ Ai i, P⁻¹ * τ a * P = τ a')
    (a₀ : A) (ha₀ : a₀ ≠ 1) :
    IsTorusDataIn c τ.range (fun i => (Ai i).map τ) P (τ a₀) π := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hπ, ⟨a₀, rfl⟩⟩
  ·
    apply odd_natCard_of_forall_odd_orderOf
    intro g
    obtain ⟨a, ha⟩ := g.2
    have hpow : g ^ N = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← ha, ← map_pow, hAN a, map_one]
      rfl
    exact Odd.of_dvd_nat hN (orderOf_dvd_of_pow_eq_one hpow)
  ·
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm a b]
  ·
    intro hbot
    have hmem : τ a₀ ∈ τ.range := ⟨a₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ha₀ (hτ (hmem.trans (map_one τ).symm))
  · intro j
    exact Subgroup.map_le_range _ _
  · intro i j hij
    rw [← Subgroup.map_sup, hAsup i j hij, ← MonoidHom.range_eq_map]
  ·
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', h1⟩ := hconjT a
    obtain ⟨a'', h2⟩ := hconjT' a
    exact ⟨by rw [h1]; exact ⟨a', rfl⟩, by rw [h2]; exact ⟨a'', rfl⟩⟩
  ·
    intro i
    constructor
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨b', hb', h1⟩ := hconj i b hb
      exact ⟨b', hb', h1.symm⟩
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨b', hb', h1⟩ := hconj' i b hb
      exact ⟨b', hb', h1.symm⟩

end CFSG.LocalAnalysis.RankThreeUC
