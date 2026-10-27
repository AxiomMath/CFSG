module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Q81

theorem isPGroup_quotient_iff {H : Type} [Group H] [Finite H] :
    IsPGroup 2 (H ⧸ pPrimeCore 2 H) ↔ ∀ h : H, Odd (orderOf h) → h ∈ pPrimeCore 2 H := by
  constructor
  · intro hP h hodd
    obtain ⟨k, hk⟩ := hP (QuotientGroup.mk h)
    have h1 : orderOf (QuotientGroup.mk h : H ⧸ pPrimeCore 2 H) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (QuotientGroup.mk h : H ⧸ pPrimeCore 2 H) ∣ orderOf h :=
      orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 H)) h
    have hqodd : Odd (orderOf (QuotientGroup.mk h : H ⧸ pPrimeCore 2 H)) :=
      Odd.of_dvd_nat hodd h2
    have h3 : orderOf (QuotientGroup.mk h : H ⧸ pPrimeCore 2 H) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hqodd)) h1
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  · intro h q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    have h0 : (x ^ 2 ^ a) ^ m = 1 := by rw [← pow_mul, ← hxm, pow_orderOf_eq_one]
    have h1 : x ^ 2 ^ a ∈ pPrimeCore 2 H :=
      h _ (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h0))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h1

theorem isPGroup_quotient_of_le {G : Type} [Group G] [Finite G] {K H : Subgroup G} (hKH : K ≤ H)
    (h : IsPGroup 2 (↥H ⧸ pPrimeCore 2 ↥H)) : IsPGroup 2 (↥K ⧸ pPrimeCore 2 ↥K) := by
  rw [isPGroup_quotient_iff] at h ⊢
  intro k hk
  set N : Subgroup ↥K := ((pPrimeCore 2 ↥H).map H.subtype).subgroupOf K with hN
  have hHn : (pPrimeCore 2 ↥H).Normal := inferInstance
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨n', hn', hn'e⟩ := mem_subgroupOf.mp hn
    refine mem_subgroupOf.mpr ⟨⟨g, hKH g.2⟩ * n' * ⟨g, hKH g.2⟩⁻¹, hHn.conj_mem n' hn' _, ?_⟩
    simp only [coe_subtype, coe_mul, coe_inv] at hn'e ⊢
    rw [hn'e]
  have hNc : Nat.Coprime 2 (Nat.card N) := by
    have hle : N.map K.subtype ≤ (pPrimeCore 2 ↥H).map H.subtype := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact mem_subgroupOf.mp hy
    have hd : Nat.card N ∣ Nat.card (pPrimeCore 2 ↥H) := by
      rw [← card_map_of_injective K.subtype_injective,
        ← card_map_of_injective (f := H.subtype) H.subtype_injective]
      exact card_dvd_of_le hle
    exact Nat.Coprime.coprime_dvd_right hd pPrimeCore_coprime_card
  have hNle : N ≤ pPrimeCore 2 ↥K := le_sSup ⟨hNn, hNc⟩
  apply hNle
  have hk' : Odd (orderOf (⟨k, hKH k.2⟩ : ↥H)) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hk
  exact mem_subgroupOf.mpr ⟨⟨k, hKH k.2⟩, h _ hk', rfl⟩

theorem isPGroup_quotient_of_surjective {H H' : Type} [Group H] [Group H'] [Finite H]
    [Finite H'] (f : H →* H') (hf : Function.Surjective f) (h : IsPGroup 2 (H ⧸ pPrimeCore 2 H)) :
    IsPGroup 2 (H' ⧸ pPrimeCore 2 H') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isPGroup_quotient_iff] at h ⊢
  intro y hy
  have hmem : y ∈ (⊤ : Subgroup H).map f := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf]
    exact mem_top y
  obtain ⟨x, -, hx, rfl⟩ := exists_odd_preimage f hmem hy
  exact map_pPrimeCore_le f hf (mem_map_of_mem f (h x hx))

end Q81

end CFSG.ComponentClassification.HarrisLit
