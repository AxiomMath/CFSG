module

public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_odd_of_coprime_three {S : Type*} [Group S] [Finite S]
    (hS : ∀ x : S, x ^ 3 = 1) (hcard : Nat.card S ≤ 9)
    (φ : MulAut S) (hodd : Odd (orderOf φ)) (h3 : Nat.Coprime 3 (orderOf φ)) : φ = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpr⟩ : ∃ p, p.Prime ∧ p ∣ orderOf φ :=
    ⟨(orderOf φ).minFac, Nat.minFac_prime (fun h => hne (orderOf_eq_one_iff.mp h)),
      Nat.minFac_dvd _⟩
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h2 := hp.two_le
    interval_cases p
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpr)
    · exact absurd (Nat.dvd_gcd (dvd_refl 3) hpr) (by rw [h3]; decide)
    · exact absurd hp (by decide)
  let ψ := φ ^ (orderOf φ / p)
  have hψ : orderOf ψ = p := orderOf_pow_orderOf_div hodd.pos.ne' hpr
  have := Fintype.ofFinite S
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hσ : (MulAut.toPerm S ψ) ^ p ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← hψ, pow_orderOf_eq_one, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  let F : Subgroup S := MonoidHom.eqLocus (ψ : S →* S) (MonoidHom.id S)
  have hFcard : Nat.card F = (MulAut.toPerm S ψ).supportᶜ.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    exact Iff.rfl
  rw [hFcard.symm, ← Nat.card_eq_fintype_card] at hmod
  have hS3 : IsPGroup 3 S := fun x => ⟨1, by simpa using hS x⟩
  obtain ⟨k, hk⟩ := hS3.exists_card_eq
  have hFdvd : Nat.card F ∣ 3 ^ k := hk ▸ Subgroup.card_subgroup_dvd_card F
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hFdvd
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk, hj] at hmod
  have hFS : Nat.card F = Nat.card S := by
    rw [hk, hj]
    have hd : 3 ^ j ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
    have hdvd : p ∣ 3 ^ k - 3 ^ j := (Nat.modEq_iff_dvd' hd).mp hmod
    by_contra hne'
    have hlt : 3 ^ j < 3 ^ k := lt_of_le_of_ne hd hne'
    have hple : p ≤ 3 ^ k - 3 ^ j := Nat.le_of_dvd (by omega) hdvd
    have hp8 : p ≤ 8 := by
      interval_cases k <;> interval_cases j <;> omega
    interval_cases p <;> interval_cases k <;> interval_cases j <;> first | omega | norm_num at hp
  have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F hFS
  have hψ1 : ψ = 1 := by
    ext x
    exact (Subgroup.eq_top_iff' F).mp hFtop x
  rw [hψ1, orderOf_one] at hψ
  omega

theorem exists_normal_index_three_of_odd {X : Type*} [Group X] [Finite X]
    (hodd : Odd (Nat.card X)) (S : Sylow 3 X) (hS : ∀ x ∈ (S : Subgroup X), x ^ 3 = 1)
    (hcomm : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x)
    (hcard : Nat.card (S : Subgroup X) = 3 ∨ Nat.card (S : Subgroup X) = 9) :
    ∃ N : Subgroup X, N.Normal ∧ N.index = 3 := by
  have hSle : (S : Subgroup X) ≤ centralizer (S : Set X) :=
    fun g hg => mem_centralizer_iff.mpr fun h hh => hcomm h hh g hg
  have hcommS : ∀ a b : ↥(S : Subgroup X), a * b = b * a :=
    fun a b => Subtype.ext (hcomm a a.2 b b.2)
  let f := (S : Subgroup X).normalizerMonoidHom
  have hcop : Nat.Coprime 3 f.ker.index := by
    rw [normalizerMonoidHom_ker]
    refine Nat.Coprime.coprime_dvd_right
      (relIndex_dvd_of_le_left _ hSle) (Nat.Coprime.coprime_dvd_right
        (relIndex_dvd_index_of_le S.le_normalizer) ?_)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr S.not_dvd_index
  have hN : normalizer (S : Set X) ≤ centralizer (S : Set X) := by
    intro n hn
    let x : normalizer (S : Set X) := ⟨n, hn⟩
    have h1 : orderOf (f x) ∣ f.ker.index := by
      rw [index_ker]
      exact Subgroup.orderOf_dvd_natCard _ ⟨x, rfl⟩
    have h2 : orderOf (f x) ∣ Nat.card X :=
      (orderOf_map_dvd f x).trans (by
        rw [← Subgroup.orderOf_coe]
        exact _root_.orderOf_dvd_natCard _)
    have hφ : f x = 1 := eq_one_of_odd_of_coprime_three
      (fun y => Subtype.ext (hS y y.2)) (by omega) (f x) (hodd.of_dvd_nat h2)
      (Nat.Coprime.coprime_dvd_right h1 hcop)
    have hker : x ∈ f.ker := hφ
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at hker
    exact hker
  have hcompl := MonoidHom.ker_transferSylow_isComplement' S hN
  let τ := MonoidHom.transferSylow S hN
  have hsurj : Function.Surjective τ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [← index_ker, hcompl.symm.index_eq_card]
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Subgroup ↥(S : Subgroup X), S₀.index = 3 := by
    rcases hcard with h | h
    · exact ⟨⊥, by rw [index_bot]; exact h⟩
    · obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 1) (G := ↥(S : Subgroup X))
        (by rw [pow_one]; exact h ▸ (by norm_num : 3 ∣ 9))
      refine ⟨K, ?_⟩
      have := card_mul_index K
      rw [hK, h] at this
      omega
  refine ⟨S₀.comap τ, ?_, ?_⟩
  · have : S₀.Normal := ⟨fun n hn g => by
      rwa [hcommS g n, mul_inv_cancel_right]⟩
    exact this.comap τ
  · rw [index_comap_of_surjective S₀ hsurj, hS₀]

end CFSG.LocalAnalysis.RankThreeUC
