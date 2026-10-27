module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Tower

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal Outer)

private lemma cardLemma_coprime_pow_or {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k m n : ℕ)
    (hn : 0 < n) (hn4 : n ≤ 4) : Nat.Coprime (p ^ k) n ∨ Nat.Coprime (2 ^ m) n := by
  have h2 : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  interval_cases n
  · exact Or.inl (Nat.coprime_one_right _)
  · exact Or.inl h2
  · exact Or.inr (Nat.Coprime.pow_left m (by norm_num))
  · exact Or.inl (Nat.Coprime.pow_right 2 h2)

private lemma cardLemma_eq_one_of_pow {G : Type*} [Group G] {a : G} {N : ℕ} (hN : a ^ N = 1)
    (hc : Nat.Coprime N (Nat.card G)) : a = 1 :=
  orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hN) (orderOf_dvd_natCard a))

theorem outTwoTowerAt_of_card_outer_le_four {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Nat.card (Outer K) ≤ 4) : OutTwoTowerAt K p := by
  refine ⟨⊤, fun _ _ _ => Subgroup.mem_top _, ?_⟩
  rintro α ⟨k, hk⟩ δ _ ⟨m, hm⟩
  haveI : (inner K).Normal := inner_normal K
  haveI : Finite (MulAut K) := MulEquiv.finite_left
  let π : MulAut K →* MulAut K ⧸ inner K := QuotientGroup.mk' (inner K)
  have hk' : π α ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hm' : π δ ^ (2 ^ m) = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hm
  have hpos : 0 < Nat.card (MulAut K ⧸ inner K) := Nat.card_pos
  have hclaim : π α = 1 ∨ π δ = 1 := by
    rcases cardLemma_coprime_pow_or hp hp2 k m _ hpos hcard with h | h
    · exact Or.inl (cardLemma_eq_one_of_pow hk' h)
    · exact Or.inr (cardLemma_eq_one_of_pow hm' h)
  have key : π (α * δ * α⁻¹ * δ⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rcases hclaim with h | h <;> simp [h]
  exact (QuotientGroup.eq_one_iff _).1 key

end CFSG.LocalAnalysis.GLTheoremA
