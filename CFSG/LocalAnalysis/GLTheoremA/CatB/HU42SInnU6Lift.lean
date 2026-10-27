module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

theorem card_comap_of_surjective {G S : Type} [Group G] [Group S] [Finite G] [Finite S]
    {π : G →* S} (hπ : Function.Surjective π) (H : Subgroup S) :
    Nat.card (H.comap π) = Nat.card π.ker * Nat.card H := by
  have h1 := Subgroup.card_mul_index (H.comap π)
  have h2 := Subgroup.card_mul_index H
  have h3 := Subgroup.card_ker_mul_card_range π
  rw [MonoidHom.range_eq_top.2 hπ, Subgroup.card_top] at h3
  rw [Subgroup.index_comap_of_surjective (H := H) hπ] at h1
  have key : Nat.card (H.comap π) * H.index = (Nat.card π.ker * Nat.card H) * H.index := by
    rw [h1, mul_assoc, h2, h3]
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) key

theorem exists_two_normal {G S : Type} [Group G] [Group S] [Finite G] {π : G →* S}
    (hπ : Function.Surjective π) (hk : Nat.card π.ker = 3)
    (hc : ∀ z ∈ π.ker, ∀ x : G, x * z = z * x)
    {T : Subgroup S} (hT : IsPGroup 2 T) (hTne : T ≠ ⊥)
    {E : Subgroup S} (hN : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T) :
    ∃ T₀ : Subgroup G, IsPGroup 2 T₀ ∧ T₀ ≠ ⊥ ∧
      ∀ p ∈ E.comap π, ∀ t ∈ T₀, p * t * p⁻¹ ∈ T₀ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI : Finite S := Finite.of_surjective π hπ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hT
  have hTcard1 : Nat.card T ≠ 1 := fun h => hTne (Subgroup.card_eq_one.1 h)
  set Th : Subgroup G := T.comap π with hTh
  have hThcard : Nat.card Th = 3 * 2 ^ a := by
    rw [hTh, card_comap_of_surjective hπ, hk, ha, mul_comm]
  have hdvd : 2 ^ a ∣ Nat.card Th := ⟨3, by rw [hThcard, mul_comm]⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Th) 2 hdvd
  set T₀ : Subgroup G := K.map Th.subtype with hT₀
  have hT₀card : Nat.card T₀ = 2 ^ a := by
    rw [hT₀, Subgroup.card_map_of_injective Th.subtype_injective, hK]
  have hT₀le : ∀ x ∈ T₀, x ∈ Th := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact k.2
  have hZTh : ∀ z ∈ π.ker, z ∈ Th := by
    intro z hz
    rw [hTh, Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]
    exact T.one_mem
  have hord3 : ∀ z ∈ π.ker, z ^ 3 = 1 := by
    intro z hz
    have := orderOf_dvd_natCard (⟨z, hz⟩ : π.ker)
    rw [hk, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hord2 : ∀ t ∈ T₀, t ^ (2 ^ a) = 1 := by
    intro t ht
    have := orderOf_dvd_natCard (⟨t, ht⟩ : T₀)
    rw [hT₀card, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hcop : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have hZT₀ : ∀ u : G, u ∈ π.ker → u ∈ T₀ → u = 1 := by
    intro u hu hu₀
    have h1 : orderOf u ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 (hord3 u hu)
    have h2 : orderOf u ∣ 2 ^ a := orderOf_dvd_iff_pow_eq_one.2 (hord2 u hu₀)
    have h3 : orderOf u ∣ Nat.gcd 3 (2 ^ a) := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  let φ : π.ker × T₀ → Th := fun p =>
    ⟨p.1.1 * p.2.1, Subgroup.mul_mem _ (hZTh p.1.1 p.1.2) (hT₀le p.2.1 p.2.2)⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨⟨z, hz⟩, ⟨t, ht⟩⟩ ⟨⟨z', hz'⟩, ⟨t', ht'⟩⟩ h
    have h' : z * t = z' * t' := congrArg Subtype.val h
    have hcomm : z'⁻¹ * z = t' * t⁻¹ := by
      calc z'⁻¹ * z = z'⁻¹ * (z * t) * t⁻¹ := by group
        _ = z'⁻¹ * (z' * t') * t⁻¹ := by rw [h']
        _ = t' * t⁻¹ := by group
    have hu : z'⁻¹ * z = 1 := by
      have hu1 : z'⁻¹ * z ∈ π.ker := π.ker.mul_mem (π.ker.inv_mem hz') hz
      have hu2 : z'⁻¹ * z ∈ T₀ := by
        rw [hcomm]
        exact T₀.mul_mem ht' (T₀.inv_mem ht)
      exact hZT₀ _ hu1 hu2
    have hzz : z = z' := (inv_mul_eq_one.1 hu).symm
    have htt : t = t' := by
      rw [hzz] at h'
      exact mul_left_cancel h'
    subst hzz
    subst htt
    rfl
  have hφbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hφinj, ?_⟩
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hk, hT₀card, hThcard]
  have hkey : ∀ x ∈ Th, x ^ (2 ^ a) = 1 → x ∈ T₀ := by
    intro x hx hxn
    obtain ⟨⟨⟨z, hz⟩, ⟨t, ht⟩⟩, hzt⟩ := hφbij.2 ⟨x, hx⟩
    have hxzt : x = z * t := (congrArg Subtype.val hzt).symm
    have hzn : z ^ (2 ^ a) = 1 := by
      have h := hxn
      rw [hxzt, Commute.mul_pow (hc z hz t).symm, hord2 t ht, mul_one] at h
      exact h
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 (hord3 z hz)
      have h2 : orderOf z ∣ 2 ^ a := orderOf_dvd_iff_pow_eq_one.2 hzn
      have h3 : orderOf z ∣ Nat.gcd 3 (2 ^ a) := Nat.dvd_gcd h1 h2
      rw [hcop.gcd_eq_one] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    rw [hxzt, hz1, one_mul]
    exact ht
  refine ⟨T₀, ?_, ?_, ?_⟩
  · exact (IsPGroup.iff_card).2 ⟨a, hT₀card⟩
  · intro h
    have h1 : Nat.card T₀ = 1 := by rw [h, Subgroup.card_bot]
    rw [hT₀card] at h1
    have ha0 : a = 0 := by
      by_contra hne
      have := Nat.one_lt_two_pow hne
      omega
    apply hTcard1
    rw [ha, ha0, pow_zero]
  · intro p hp t ht
    apply hkey
    · rw [hTh, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hN _ hp _ (hT₀le t ht)
    · rw [conj_pow, hord2 t ht, mul_one, mul_inv_cancel]

end CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

end
