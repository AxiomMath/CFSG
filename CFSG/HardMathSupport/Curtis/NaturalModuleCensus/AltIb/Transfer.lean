module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeGroup

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.AGLEmbedding.ToralCensus

theorem isCyclic_of_isPGroup_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : ¬ p ^ 2 ∣ Nat.card G) {A : Subgroup G} (hA : IsPGroup p A) :
    IsCyclic A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra hlt
    apply h
    have h1 : p ^ 2 ∣ p ^ n := pow_dvd_pow p (by omega)
    exact h1.trans (hn ▸ A.card_subgroup_dvd_card)
  interval_cases n
  · have : A = ⊥ := Subgroup.eq_bot_of_card_eq A (by simpa using hn)
    rw [this]
    infer_instance
  · exact isCyclic_of_prime_card (by simpa using hn)

theorem eq_one_of_commute_of_perfect_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hG : ¬ p ^ 2 ∣ Nat.card G) {V : Subgroup G} (hV : ⁅V, V⁆ = V)
    (hpV : p ∣ Nat.card V) {y : G} (hyp : y ^ p = 1) (hy : ∀ v ∈ V, v * y = y * v) :
    y = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : ∀ Q : Subgroup G, Q ≤ V → IsPGroup p Q → IsCyclic Q := fun Q _ hQ =>
    isCyclic_of_isPGroup_of_not_sq_dvd hp hG hQ
  have hcycT : ∀ Q : Subgroup G, Q ≤ ⊤ → IsPGroup p Q → IsCyclic Q := fun Q _ hQ =>
    isCyclic_of_isPGroup_of_not_sq_dvd hp hG hQ
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := V) p hpV
  have hr' : orderOf (r : G) = p := by rw [Subgroup.orderOf_coe]; exact hr
  have hyr : y ∈ Subgroup.zpowers (r : G) :=
    mem_zpowers_of_commute_of_pow hcycT trivial trivial (hy r r.2).symm hyp hr'
  have hyV : y ∈ V := (Subgroup.zpowers_le.2 r.2) hyr
  exact eq_one_of_commute_of_perfect_cyclic hp hV hcyc hyV (fun a ha => hy a ha) hyp

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
