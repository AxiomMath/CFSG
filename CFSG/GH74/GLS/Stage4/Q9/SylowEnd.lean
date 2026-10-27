module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Simproc.Divisors

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem sylow1039_not_mod_418 (d : ℕ) (hd : d ∣ 245742) : d % 1039 ≠ 418 := by
  have h : (245742 : ℕ) = 42 * 5851 := by norm_num
  rw [h] at hd
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hd
  have hp : Nat.Prime 5851 := by norm_num
  have hy' : y ∈ Nat.divisors 42 := Nat.mem_divisors.mpr ⟨hy, by norm_num⟩
  simp only [Nat.divisors_ofNat] at hy'
  rcases (Nat.dvd_prime hp).mp hz with rfl | rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem sylow1039_arith (i n r c : ℕ) (h1 : i % 1039 = 1)
    (h2 : i * n = 518400 * (7 * 1039 * 5851)) (h3 : r * c = n)
    (h4 : r ∣ 1038) (h5 : c ∣ 7 * 1039 * 5851) (h6 : 1039 ∣ n) : False := by
  have hrn : r ∣ 518400 * (7 * 1039 * 5851) := by
    rw [← h2, ← h3]
    exact Dvd.dvd.mul_left (Dvd.intro c rfl) i
  have hr6 : r ∣ 6 := by
    have := Nat.dvd_gcd h4 hrn
    have h : Nat.gcd 1038 (518400 * (7 * 1039 * 5851)) = 6 := by norm_num
    rwa [h] at this
  have hn : n ∣ 1039 * 245742 := by
    have := mul_dvd_mul hr6 h5
    rw [h3] at this
    simpa [show 6 * (7 * 1039 * 5851) = 1039 * 245742 by norm_num] using this
  obtain ⟨d, rfl⟩ := h6
  have hd : d ∣ 245742 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hn
  have h7 : i * d = 518400 * 7 * 5851 := by
    have : 1039 * (i * d) = 1039 * (518400 * 7 * 5851) := by
      calc 1039 * (i * d) = i * (1039 * d) := by ring
        _ = 518400 * (7 * 1039 * 5851) := h2
        _ = 1039 * (518400 * 7 * 5851) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have h8 : d % 1039 = 418 := by
    have h9 : (i * d) % 1039 = d % 1039 := by
      rw [Nat.mul_mod, h1, one_mul, Nat.mod_mod]
    rw [← h9, h7]
  exact sylow1039_not_mod_418 d hd h8

theorem sylow1039_card {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 518400 * (7 * 1039 * 5851)) (Q : Sylow 1039 G) :
    Nat.card Q = 1039 := by
  have hp : Fact (Nat.Prime 1039) := ⟨by norm_num⟩
  have h : (Nat.card G).factorization 1039 = 1 := by
    rw [hcard, show 518400 * (7 * 1039 * 5851) = 1039 * (518400 * 7 * 5851) by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      hp.out.factorization_self, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [Q.card_eq_multiplicity, h, pow_one]

theorem relIndex_centralizer_normalizer_dvd_totient {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [IsCyclic Q] :
    (centralizer (Q : Set G)).relIndex (normalizer (Q : Set G)) ∣ Nat.totient (Nat.card Q) := by
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective Q.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, ← relIndex] at key
  rwa [IsCyclic.card_mulAut] at key

theorem not_dvd_card_centralizer_of_sylow1039 {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : Nat.card Q = 1039)
    (hcent : ∀ y : G, (orderOf y = 2 ∨ orderOf y = 3 ∨ orderOf y = 5) →
      ¬ 1039 ∣ Nat.card (centralizer ({y} : Set G))) {r : ℕ} (hr : r.Prime)
    (hr' : r = 2 ∨ r = 3 ∨ r = 5) : ¬ r ∣ Nat.card (centralizer (Q : Set G)) := by
  intro hdvd
  have := Fact.mk hr
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hy : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
  refine hcent (x : G) (by rcases hr' with rfl | rfl | rfl <;> simp [hy]) ?_
  have hle : Q ≤ centralizer ({(x : G)} : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (mem_centralizer_iff.mp x.2 q hq).symm
  have := card_dvd_of_le hle
  rwa [hQ] at this

theorem sylow1039_false (G : Type*) [Group G] [Finite G]
    (hcard : Nat.card G = 518400 * (7 * 1039 * 5851))
    (hcent : ∀ y : G, (orderOf y = 2 ∨ orderOf y = 3 ∨ orderOf y = 5) →
      ¬ 1039 ∣ Nat.card (Subgroup.centralizer ({y} : Set G))) : False := by
  have hp : Fact (Nat.Prime 1039) := ⟨by norm_num⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 1039 G) := inferInstance
  have hQ : Nat.card Q = 1039 := sylow1039_card hcard Q
  have hcyc : IsCyclic Q := isCyclic_of_prime_card hQ
  have hCN : centralizer (Q : Set G) ≤ normalizer (Q : Set G) := centralizer_le_normalizer _
  have hQN : (Q : Subgroup G) ≤ normalizer (Q : Set G) := Q.le_normalizer
  refine sylow1039_arith (normalizer (Q : Set G)).index (Nat.card (normalizer (Q : Set G)))
    ((centralizer (Q : Set G)).relIndex (normalizer (Q : Set G)))
    (Nat.card (centralizer (Q : Set G))) ?_ ?_ ?_ ?_ ?_ ?_
  · have h1 := card_sylow_modEq_one 1039 G
    rw [Q.card_eq_index_normalizer] at h1
    exact h1
  · rw [← hcard]
    exact (normalizer (Q : Set G)).index_mul_card
  · have := relIndex_mul_card (H := centralizer (Q : Set G)) (K := normalizer (Q : Set G))
    rwa [inf_eq_left.mpr hCN] at this
  · have := relIndex_centralizer_normalizer_dvd_totient (Q : Subgroup G)
    rwa [hQ, Nat.totient_prime hp.out] at this
  · have hdvd : Nat.card (centralizer (Q : Set G)) ∣ 518400 * (7 * 1039 * 5851) := by
      rw [← hcard]; exact card_subgroup_dvd_card _
    have hc2 := not_dvd_card_centralizer_of_sylow1039 hQ hcent (r := 2) (by norm_num) (by simp)
    have hc3 := not_dvd_card_centralizer_of_sylow1039 hQ hcent (r := 3) (by norm_num) (by simp)
    have hc5 := not_dvd_card_centralizer_of_sylow1039 hQ hcent (r := 5) (by norm_num) (by simp)
    have hcop : Nat.Coprime (Nat.card (centralizer (Q : Set G))) 518400 := by
      have e : (518400 : ℕ) = 2 ^ 8 * 3 ^ 4 * 5 ^ 2 := by norm_num
      rw [e]
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
      · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hc2).symm
      · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hc3).symm
      · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hc5).symm
    exact hcop.dvd_of_dvd_mul_left hdvd
  · have := card_dvd_of_le hQN
    rwa [hQ] at this

end CFSG.GH74.GLS.Stage4.Q9
