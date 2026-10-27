module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ComponentClassification
open CFSG.ClassicalInvolution.Q3

section OddLift

variable {K : Type} [Group K]

theorem exists_oddLift (hZ : IsPGroup 2 (Subgroup.center K)) {n : K ⧸ Subgroup.center K} {m : ℕ}
    (hm : Odd m) (hn : n ^ m = 1) :
    ∃ ν : K, (QuotientGroup.mk ν : K ⧸ Subgroup.center K) = n ∧ ν ^ m = 1 := by
  obtain ⟨ν₁, rfl⟩ := QuotientGroup.mk_surjective n
  have h1 : ν₁ ^ m ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, QuotientGroup.mk'_apply]
    exact hn
  obtain ⟨e, he⟩ := hZ ⟨ν₁ ^ m, h1⟩
  have he' : (ν₁ ^ m) ^ (2 ^ e) = 1 := congrArg Subtype.val he
  have hcop : IsCoprime ((2 : ℤ) ^ e) (m : ℤ) := by
    have : Nat.Coprime (2 ^ e) m := (Nat.coprime_two_left.mpr hm).pow_left e
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨ν₁ ^ (a * 2 ^ e), ?_, ?_⟩
  · rw [QuotientGroup.mk_zpow]
    have e1 : ((a * 2 ^ e : ℤ)) = 1 - b * m := by linarith
    rw [e1, zpow_sub, zpow_one, zpow_mul', zpow_natCast, hn, one_zpow, inv_one, mul_one]
  · have h2 : ν₁ ^ (m * 2 ^ e) = 1 := by rw [pow_mul]; exact he'
    rw [← zpow_natCast, ← zpow_mul]
    have e1 : (a * 2 ^ e * m : ℤ) = ((m * 2 ^ e : ℕ) : ℤ) * a := by push_cast; ring
    rw [e1, zpow_mul, zpow_natCast, h2, one_zpow]

theorem eq_one_of_odd_pow_of_two_pow {g : K} {m e : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (hge : g ^ (2 ^ e) = 1) : g = 1 := by
  have h1 : orderOf g ∣ m := orderOf_dvd_of_pow_eq_one hgm
  have h2 : orderOf g ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hge
  have h3 : Nat.Coprime m (2 ^ e) := (Nat.coprime_two_right.mpr hm).pow_right e
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2)

theorem exists_fixed_oddLift (hZ : IsPGroup 2 (Subgroup.center K)) (σ : MulAut K)
    {n : K ⧸ Subgroup.center K} (hn : n ∈ fixedSubgroup (autToCentralQuotient K σ)) {m : ℕ}
    (hm : Odd m) (hnm : n ^ m = 1) :
    ∃ ν : K, (QuotientGroup.mk ν : K ⧸ Subgroup.center K) = n ∧ ν ^ m = 1 ∧ σ ν = ν := by
  obtain ⟨ν, rfl, hν⟩ := exists_oddLift hZ hm hnm
  refine ⟨ν, rfl, hν, ?_⟩
  have h1 : (QuotientGroup.mk (σ ν) : K ⧸ Subgroup.center K) = QuotientGroup.mk ν := hn
  have hz : ν⁻¹ * σ ν ∈ Subgroup.center K := QuotientGroup.eq.mp h1.symm
  set z := ν⁻¹ * σ ν with hzdef
  have hσν : σ ν = ν * z := by rw [hzdef]; group
  have hzm : z ^ m = 1 := by
    have h2 : (σ ν) ^ m = 1 := by rw [← map_pow, hν, map_one]
    rw [hσν] at h2
    have hc : Commute ν z := Subgroup.mem_center_iff.mp hz ν
    rw [hc.mul_pow, hν, one_mul] at h2
    exact h2
  obtain ⟨e, he⟩ := hZ ⟨z, hz⟩
  have hz1 : z = 1 := eq_one_of_odd_pow_of_two_pow hm hzm (congrArg Subtype.val he)
  rw [hσν, hz1, mul_one]

end OddLift

section Blocks

variable {K : Type} [Group K] [Finite K]

theorem oddCoreIn_fixed_eq_bot_of_blocks (hZ : IsPGroup 2 (Subgroup.center K)) (σ : MulAut K)
    {ι : Type} (L : ι → Subgroup K) (hLB : ∀ i, L i ≤ fixedSubgroup σ)
    (hnorm : ∀ i, ∀ b ∈ fixedSubgroup σ, ∀ x ∈ L i, b * x * b⁻¹ ∈ L i)
    (hno : ∀ i, oddCoreIn ((L i).map (QuotientGroup.mk' (Subgroup.center K))) = ⊥)
    (hcent : ∀ ν ∈ fixedSubgroup σ, (∀ i, ∀ x ∈ L i, ν * x = x * ν) →
      ∃ e : ℕ, ν ^ (2 ^ e) = 1) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient K σ)) = ⊥ := by
  set Z := Subgroup.center K with hZdef
  set π := QuotientGroup.mk' Z with hπ
  set C := fixedSubgroup (autToCentralQuotient K σ) with hC
  set N := oddCoreIn C with hN
  have hker : ∀ y : K, π y = 1 → y ∈ Z := fun y hy => (QuotientGroup.eq_one_iff y).mp hy
  have hlift : ∀ n ∈ N, ∃ ν : K, π ν = n ∧ σ ν = ν ∧ ∃ m : ℕ, Odd m ∧ ν ^ m = 1 := by
    intro n hn
    have hm : Odd (orderOf n) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn C) (Subgroup.orderOf_dvd_natCard N hn)
    obtain ⟨ν, hνn, hνm, hσν⟩ :=
      exists_fixed_oddLift hZ σ (oddCoreIn_le C hn) hm (pow_orderOf_eq_one n)
    exact ⟨ν, hνn, hσν, _, hm, hνm⟩
  have hnormN : ∀ y ∈ C, ∀ w, w ∈ N ↔ y * w * y⁻¹ ∈ N := by
    intro y hy w
    refine ⟨fun hw => conj_mem_oddCoreIn hy hw, fun hw => ?_⟩
    have := conj_mem_oddCoreIn (C.inv_mem hy) hw
    simpa [mul_assoc] using this
  have hcommL : ∀ ν : K, π ν ∈ N → σ ν = ν → (∃ m : ℕ, Odd m ∧ ν ^ m = 1) →
      ∀ i, ∀ x ∈ L i, ν * x = x * ν := by
    intro ν hν hσν ⟨k, hk, hνk⟩ i x hx
    set Li := (L i).map π with hLi
    have hLiC : Li ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : σ y = y := hLB i hy
      show autToCentralQuotient K σ (QuotientGroup.mk y) = QuotientGroup.mk y
      rw [autToCentralQuotient_mk, hy']
    have hπx : π x ∈ Li := ⟨x, hx, rfl⟩
    have hconj : ∀ y ∈ Li, π ν * y * (π ν)⁻¹ ∈ Li := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨ν * y * ν⁻¹, hnorm i ν hσν y hy, by simp⟩
    have hmemN : π ν * π x * (π ν)⁻¹ * (π x)⁻¹ ∈ N := by
      have h1 : π x * (π ν)⁻¹ * (π x)⁻¹ ∈ N := by
        have := conj_mem_oddCoreIn (hLiC hπx) (N.inv_mem hν)
        simpa [mul_assoc] using this
      have h2 := N.mul_mem hν h1
      simpa [mul_assoc] using h2
    have hmemL : π ν * π x * (π ν)⁻¹ * (π x)⁻¹ ∈ Li :=
      Li.mul_mem (hconj _ hπx) (Li.inv_mem hπx)
    have hle : N ⊓ Li ≤ oddCoreIn Li := by
      refine le_oddCoreIn_of_normalizes inf_le_right ?_
        ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · rintro ⟨hwN, hwL⟩
        exact ⟨conj_mem_oddCoreIn (hLiC hy) hwN,
          Li.mul_mem (Li.mul_mem hy hwL) (Li.inv_mem hy)⟩
      · rintro ⟨hwN, hwL⟩
        refine ⟨(hnormN y (hLiC hy) w).mpr hwN, ?_⟩
        have := Li.mul_mem (Li.mul_mem (Li.inv_mem hy) hwL) hy
        simpa [mul_assoc] using this
    have hcomm1 : π ν * π x * (π ν)⁻¹ * (π x)⁻¹ = 1 := by
      have h1 := hle ⟨hmemN, hmemL⟩
      rw [hno i, Subgroup.mem_bot] at h1
      exact h1
    have hz : ν * x * ν⁻¹ * x⁻¹ ∈ Z := hker _ (by simpa only [map_mul, map_inv] using hcomm1)
    exact commute_of_odd_pow_mem_center hZ hk (by rw [hνk]; exact Z.one_mem) hz
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨ν, rfl, hσν, m, hm, hνm⟩ := hlift n hn
  obtain ⟨e, he⟩ := hcent ν hσν (hcommL ν hn hσν ⟨m, hm, hνm⟩)
  have : ν = 1 := eq_one_of_odd_pow_of_two_pow hm hνm he
  rw [this, map_one]

end Blocks

end CFSG.ClassicalInvolution.Q3.Q3NM
