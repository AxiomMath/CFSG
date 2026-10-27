module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

theorem swap_order_three_five {K : Type*} [Group K] [Finite K] {z : K} {B S₁ S₂ : Subgroup K}
    (h : Setting K z B) (hs : SwapData K z B S₁ S₂)
    (hno₁ : ∀ a : ↥S₁, orderOf a ≠ 15) (hno₂ : ∀ a : ↥S₂, orderOf a ≠ 15)
    {g k : K} (hg : orderOf g = 3) (hk : orderOf k = 5) (hgk : g * k = k * g)
    (hgE : g ∈ layer K) (hkE : k ∈ layer K) :
    (g ∈ S₁ ∧ k ∈ S₂) ∨ (g ∈ S₂ ∧ k ∈ S₁) := by
  have hdisj : S₁ ⊓ S₂ = ⊥ := hs.disjoint h
  have hle : S₂ ≤ centralizer (S₁ : Set K) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hs.commute a ha b hb
  have decomp : ∀ {x : K}, x ∈ layer K → ∃ a ∈ S₁, ∃ b ∈ S₂, x = a * b := by
    intro x hx
    have hAC : S₁ ≤ normalizer (S₂ : Set K) := fun a ha =>
      centralizer_le_normalizer _ ((Subgroup.le_centralizer_iff.mp hle) ha)
    rw [hs.layer_eq] at hx
    have hx' : x ∈ ((S₁ ⊔ S₂ : Subgroup K) : Set K) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S₁ S₂ hAC] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    exact ⟨a, ha, b, hb, hab.symm⟩
  obtain ⟨a₁, ha₁, b₁, hb₁, hgab⟩ := decomp hgE
  obtain ⟨a₂, ha₂, b₂, hb₂, hkab⟩ := decomp hkE
  have huniq : ∀ {a a' b b' : K}, a ∈ S₁ → a' ∈ S₁ → b ∈ S₂ → b' ∈ S₂ →
      a * b = a' * b' → a = a' ∧ b = b' := by
    intro a a' b b' ha ha' hb hb' heq
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [heq]
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ S₁ ⊓ S₂ := by
      refine ⟨S₁.mul_mem (S₁.inv_mem ha') ha, ?_⟩
      rw [h1]
      exact S₂.mul_mem hb' (S₂.inv_mem hb)
    rw [hdisj, mem_bot] at hmem
    have h2 : b' * b⁻¹ = 1 := by rw [← h1, hmem]
    exact ⟨(eq_of_inv_mul_eq_one hmem).symm, ((mul_inv_eq_one).mp h2).symm⟩
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hk5 : k ^ 5 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
  have hpow : ∀ {a b : K} {n : ℕ}, a ∈ S₁ → b ∈ S₂ → (a * b) ^ n = 1 →
      a ^ n = 1 ∧ b ^ n = 1 := by
    intro a b n ha hb hab
    have hmul : a ^ n * b ^ n = 1 := by
      rw [← Commute.mul_pow (show Commute a b from hs.commute a ha b hb) n]
      exact hab
    constructor
    · have hmem : a ^ n ∈ S₁ ⊓ S₂ := by
        refine ⟨S₁.pow_mem ha n, ?_⟩
        have hEq : a ^ n = (b ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hmul
        rw [hEq]
        exact S₂.inv_mem (S₂.pow_mem hb n)
      rwa [hdisj, mem_bot] at hmem
    · have hmem : b ^ n ∈ S₁ ⊓ S₂ := by
        refine ⟨?_, S₂.pow_mem hb n⟩
        have hEq : b ^ n = (a ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hmul
        rw [hEq]
        exact S₁.inv_mem (S₁.pow_mem ha n)
      rwa [hdisj, mem_bot] at hmem
  have hg3ab : (a₁ * b₁) ^ 3 = 1 := by rw [← hgab]; exact hg3
  have hk5ab : (a₂ * b₂) ^ 5 = 1 := by rw [← hkab]; exact hk5
  obtain ⟨ha1pow, hb1pow⟩ := hpow (n := 3) ha₁ hb₁ hg3ab
  obtain ⟨ha2pow, hb2pow⟩ := hpow (n := 5) ha₂ hb₂ hk5ab
  have horder3 : ∀ {x : K}, x ^ 3 = 1 → x ≠ 1 → orderOf x = 3 := by
    intro x hx3 hx1
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx3 hx1
  have horder5 : ∀ {x : K}, x ^ 5 = 1 → x ≠ 1 → orderOf x = 5 := by
    intro x hx5 hx1
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx5 hx1
  have hgk1 : g * k = (a₁ * a₂) * (b₁ * b₂) := by
    calc g * k = a₁ * (b₁ * (a₂ * b₂)) := by rw [hgab, hkab]; group
      _ = a₁ * ((b₁ * a₂) * b₂) := by group
      _ = a₁ * ((a₂ * b₁) * b₂) := by rw [← hs.commute a₂ ha₂ b₁ hb₁]
      _ = (a₁ * a₂) * (b₁ * b₂) := by group
  have hkg1 : k * g = (a₂ * a₁) * (b₂ * b₁) := by
    calc k * g = a₂ * (b₂ * (a₁ * b₁)) := by rw [hkab, hgab]; group
      _ = a₂ * ((b₂ * a₁) * b₁) := by group
      _ = a₂ * ((a₁ * b₂) * b₁) := by rw [← hs.commute a₁ ha₁ b₂ hb₂]
      _ = (a₂ * a₁) * (b₂ * b₁) := by group
  have hcomm_prod : (a₁ * a₂) * (b₁ * b₂) = (a₂ * a₁) * (b₂ * b₁) :=
    hgk1.symm.trans (hgk.trans hkg1)
  have huniq_gk := huniq (S₁.mul_mem ha₁ ha₂) (S₁.mul_mem ha₂ ha₁)
    (S₂.mul_mem hb₁ hb₂) (S₂.mul_mem hb₂ hb₁) hcomm_prod
  have hg_ne : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    omega
  have hk_ne : k ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hk
    omega
  by_cases ha1 : a₁ = 1
  ·
    right
    have hb1_ne : b₁ ≠ 1 := by
      intro hb1
      apply hg_ne
      rw [hgab, ha1, hb1, one_mul]
    have hb2_eq : b₂ = 1 := by
      by_contra hb2_ne
      have hb1o : orderOf b₁ = 3 := horder3 hb1pow hb1_ne
      have hb2o : orderOf b₂ = 5 := horder5 hb2pow hb2_ne
      have hco : (orderOf b₁).Coprime (orderOf b₂) := by rw [hb1o, hb2o]; norm_num
      have h15 : orderOf (b₁ * b₂) = 15 := by
        rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime
          (show Commute b₁ b₂ from huniq_gk.2) hco, hb1o, hb2o]
      exact hno₂ ⟨b₁ * b₂, S₂.mul_mem hb₁ hb₂⟩ (by rw [Subgroup.orderOf_mk]; exact h15)
    refine ⟨?_, ?_⟩
    · have hgeq : g = b₁ := by rw [hgab, ha1, one_mul]
      rw [hgeq]
      exact hb₁
    · have hkeq : k = a₂ := by rw [hkab, hb2_eq, mul_one]
      rw [hkeq]
      exact ha₂
  ·
    left
    have ha2_eq : a₂ = 1 := by
      by_contra ha2_ne
      have ha1o : orderOf a₁ = 3 := horder3 ha1pow ha1
      have ha2o : orderOf a₂ = 5 := horder5 ha2pow ha2_ne
      have hco : (orderOf a₁).Coprime (orderOf a₂) := by rw [ha1o, ha2o]; norm_num
      have h15 : orderOf (a₁ * a₂) = 15 := by
        rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime
          (show Commute a₁ a₂ from huniq_gk.1) hco, ha1o, ha2o]
      exact hno₁ ⟨a₁ * a₂, S₁.mul_mem ha₁ ha₂⟩ (by rw [Subgroup.orderOf_mk]; exact h15)
    have hb1_eq : b₁ = 1 := by
      have hb2_ne : b₂ ≠ 1 := by
        intro hb2
        apply hk_ne
        rw [hkab, ha2_eq, hb2, one_mul]
      by_contra hb1_ne
      have hb1o : orderOf b₁ = 3 := horder3 hb1pow hb1_ne
      have hb2o : orderOf b₂ = 5 := horder5 hb2pow hb2_ne
      have hco : (orderOf b₁).Coprime (orderOf b₂) := by rw [hb1o, hb2o]; norm_num
      have h15 : orderOf (b₁ * b₂) = 15 := by
        rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime
          (show Commute b₁ b₂ from huniq_gk.2) hco, hb1o, hb2o]
      exact hno₂ ⟨b₁ * b₂, S₂.mul_mem hb₁ hb₂⟩ (by rw [Subgroup.orderOf_mk]; exact h15)
    refine ⟨?_, ?_⟩
    · have hgeq : g = a₁ := by rw [hgab, hb1_eq, mul_one]
      rw [hgeq]
      exact ha₁
    · have hkeq : k = b₂ := by rw [hkab, ha2_eq, one_mul]
      rw [hkeq]
      exact hb₂

end CFSG.EvenSporadicStandard.HSStd.InvCent
