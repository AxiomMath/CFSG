module

public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternating

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem isSolvable_of_prime_dvd_card_eq_or_eq {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = a ∨ r = b) : Group.IsSolvable G := by
  classical
  refine isSolvable_of_card_primeFactors_le_two
    ((Finset.card_le_card fun r hr => ?_).trans (Finset.card_le_two (a := a) (b := b)))
  rw [Finset.mem_insert, Finset.mem_singleton]
  exact h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)

theorem eq_two_or_three_or_eleven_of_dvd_33792 {r : ℕ} (hr : r.Prime) (h : r ∣ 33792) :
    r = 2 ∨ r = 3 ∨ r = 11 := by
  have h' : r ∣ 2 ^ 10 * 3 * 11 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).mp h' with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h))

theorem eq_one_or_twelve_or_1024_of_dvd_3072 {n : ℕ} (h : n ∣ 3072) (h1 : n % 11 = 1) :
    n = 1 ∨ n = 12 ∨ n = 1024 := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp (show n ∣ 2 ^ 10 * 3 by norm_num; exact h)
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  rcases (Nat.dvd_prime Nat.prime_three).mp hz with rfl | rfl <;> interval_cases i <;> omega

theorem normalizer_le_centralizer_of_coprime {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hP : Nat.card P = p)
    (hcop : Nat.Coprime (Nat.card (normalizer (P : Set G))) (p - 1)) :
    normalizer (P : Set G) ≤ centralizer (P : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  have hrange : P.normalizerMonoidHom.range = ⊥ := by
    rw [← card_eq_one]
    refine Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left ?_ hcop) ?_
    · rw [← index_ker]
      exact index_dvd_card _
    · have h := card_subgroup_dvd_card P.normalizerMonoidHom.range
      rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime hp] at h
  intro g hg
  have hmem : (⟨g, hg⟩ : normalizer (P : Set G)) ∈ P.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, ← mem_bot, ← hrange]
    exact ⟨_, rfl⟩
  rw [normalizerMonoidHom_ker, mem_subgroupOf] at hmem
  exact hmem

theorem false_of_normalizer_le_centralizer {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hp : p ∣ Nat.card G)
    (hPG : Nat.card (P : Subgroup G) ≠ Nat.card G)
    (hP : normalizer (P : Set G) ≤ centralizer (P : Set G)) : False := by
  obtain ⟨K, hK, -, hindex, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hP
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with rfl | rfl
  · rw [index_bot] at hindex
    exact hPG hindex.symm
  · rw [index_top] at hindex
    exact P.ne_bot_of_dvd_card hp (card_eq_one.mp hindex.symm)

theorem no_nonabelian_simple_order_dividing_33792 {S : Type*} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ x y : S, x * y ≠ y * x) : ¬ Nat.card S ∣ 33792 := by
  intro hdvd
  classical
  have := hs
  have hnsolv : ¬ Group.IsSolvable S := fun hsolv => by
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card S → r = 2 ∨ r = 3 ∨ r = 11 := fun r hr h =>
    eq_two_or_three_or_eleven_of_dvd_33792 hr (h.trans hdvd)
  have h2 : 2 ∣ Nat.card S := by
    by_contra h
    refine hnsolv (isSolvable_of_prime_dvd_card_eq_or_eq (a := 3) (b := 11) fun r hr hrS => ?_)
    rcases hprime r hr hrS with rfl | h' | h'
    · exact absurd hrS h
    · exact Or.inl h'
    · exact Or.inr h'
  have h11 : 11 ∣ Nat.card S := by
    by_contra h
    refine hnsolv (isSolvable_of_prime_dvd_card_eq_or_eq (a := 2) (b := 3) fun r hr hrS => ?_)
    rcases hprime r hr hrS with h' | h' | rfl
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd hrS h
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 11 S) := inferInstance
  have hPcard : Nat.card (P : Subgroup S) = 11 := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact P.ne_bot_of_dvd_card h11 (card_eq_one.mp hk)
    have hk2 : k < 2 := by
      by_contra hk2
      have h121 : 11 ^ 2 ∣ 33792 := (pow_dvd_pow 11 (not_lt.mp hk2)).trans
        (hk ▸ (card_subgroup_dvd_card (P : Subgroup S)).trans hdvd)
      norm_num at h121
    rw [hk, show k = 1 by omega, pow_one]
  have hPS : Nat.card (P : Subgroup S) ≠ Nat.card S := fun h => by
    rw [← h, hPcard] at h2
    norm_num at h2
  have hmod : Nat.card (Sylow 11 S) % 11 = 1 := card_sylow_modEq_one 11 S
  have hindex : (P : Subgroup S).index ∣ 3072 := by
    have h := card_mul_index (P : Subgroup S)
    rw [hPcard] at h
    have h' : 11 * (P : Subgroup S).index ∣ 11 * 3072 := by
      rw [h]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
  have hnorm := P.card_eq_index_normalizer
  rcases eq_one_or_twelve_or_1024_of_dvd_3072 (P.card_dvd_index.trans hindex) hmod with
    h1 | h12 | h1024
  ·
    rw [h1, eq_comm, index_eq_one] at hnorm
    have : (P : Subgroup S).Normal := normalizer_eq_top_iff.mp hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup S) with hbot | htop
    · exact P.ne_bot_of_dvd_card h11 hbot
    · rw [htop, card_top] at hPS
      exact hPS rfl
  ·
    let : Fintype (Sylow 11 S) := Fintype.ofFinite _
    let φ := MulAction.toPermHom S (Sylow 11 S)
    have hφ : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker).resolve_right fun htop => ?_
      have htop' : normalizer (P : Set S) = ⊤ := eq_top_iff.mpr fun g _ => by
        have hg : φ g = 1 := (MonoidHom.mem_ker).mp (htop ▸ mem_top g)
        exact Sylow.smul_eq_iff_mem_normalizer.mp (congrArg (fun σ => σ P) hg)
      rw [htop', index_top] at hnorm
      omega
    have halt : φ.range ≤ alternatingGroup (Sylow 11 S) := by
      have hsign : (Equiv.Perm.sign.comp φ).ker = ⊤ := by
        refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Equiv.Perm.sign.comp φ).ker).resolve_left
          fun hbot => ?_
        rw [MonoidHom.ker_eq_bot_iff] at hbot
        obtain ⟨x, y, hxy⟩ := hnab
        exact hxy (hbot (by rw [map_mul, map_mul, mul_comm]))
      rintro _ ⟨g, rfl⟩
      have hg : g ∈ (Equiv.Perm.sign.comp φ).ker := hsign ▸ mem_top g
      exact Equiv.Perm.mem_alternatingGroup.mpr (MonoidHom.mem_ker.mp hg)
    have hΩ : Fintype.card (Sylow 11 S) = 11 + 1 := by
      rw [Fintype.card_eq_nat_card, h12]
    have hP' : Nat.card ((P : Subgroup S).map φ) = 11 := by
      rw [card_map_of_injective hφ, hPcard]
    have hY : Nat.card φ.range = Nat.card S :=
      (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
    have hgcd : Nat.gcd (Nat.card φ.range) (11 - 1) ∣ 2 := by
      rw [hY]
      exact (Nat.gcd_dvd_gcd_of_dvd_left _ hdvd).trans (by norm_num)
    obtain ⟨hN, hC⟩ := normalizer_inf_eq_and_centralizer_inf_eq (by norm_num) (by norm_num) hΩ
      halt (map_le_range φ _) hP' hgcd
    refine false_of_normalizer_le_centralizer P h11 hPS fun g hg => ?_
    have hφg : φ g ∈ φ.range ⊓ normalizer (((P : Subgroup S).map φ : Subgroup _) : Set _) :=
      ⟨⟨g, rfl⟩, le_normalizer_map φ (mem_map_of_mem φ hg)⟩
    rw [hN, ← hC] at hφg
    rw [mem_centralizer_iff]
    intro x hx
    apply hφ
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hφg.2 (φ x) (mem_map_of_mem φ hx)
  ·
    refine false_of_normalizer_le_centralizer P h11 hPS
      (normalizer_le_centralizer_of_coprime (by norm_num) hPcard ?_)
    have h := card_mul_index (normalizer (P : Set S))
    rw [← hnorm, h1024] at h
    have h' : Nat.card (normalizer (P : Set S)) * 1024 ∣ 33 * 1024 := by
      rw [h]
      exact hdvd
    have hN : Nat.card (normalizer (P : Set S)) ∣ 33 :=
      Nat.dvd_of_mul_dvd_mul_right (by norm_num) h'
    exact Nat.Coprime.coprime_dvd_left hN (by norm_num)

end CFSG.LocalAnalysis.ComponentInitial
