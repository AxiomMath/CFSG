module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def Refl (W : Subgroup G) (x g : G) : Prop := x * g * x⁻¹ * g ∈ W

theorem refl_one (W : Subgroup G) (x : G) : Refl W x 1 := by
  unfold Refl
  have : x * 1 * x⁻¹ * 1 = 1 := by group
  rw [this]; exact one_mem W

theorem refl_mul {W : Subgroup G} {x g₁ g₂ : G} (h₁ : g₁ ∈ normalizer (W : Set G))
    (hc : g₁ * g₂ = g₂ * g₁) (r₁ : Refl W x g₁) (r₂ : Refl W x g₂) : Refl W x (g₁ * g₂) := by
  unfold Refl at *
  have h1 : g₁⁻¹ * (x * g₂ * x⁻¹ * g₂) * g₁ ∈ W := by
    have := (mem_normalizer_iff.1 (inv_mem h₁) (x * g₂ * x⁻¹ * g₂)).1 r₂
    simpa using this
  have e : x * (g₁ * g₂) * x⁻¹ * (g₁ * g₂) =
      (x * g₁ * x⁻¹ * g₁) * (g₁⁻¹ * (x * g₂ * x⁻¹ * g₂) * g₁) * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂) := by
    group
  have e2 : g₁⁻¹ * g₂⁻¹ * g₁ * g₂ = 1 := by
    have : g₁ * g₂ = g₂ * g₁ := hc
    calc g₁⁻¹ * g₂⁻¹ * g₁ * g₂ = g₁⁻¹ * g₂⁻¹ * (g₁ * g₂) := by group
      _ = g₁⁻¹ * g₂⁻¹ * (g₂ * g₁) := by rw [this]
      _ = 1 := by group
  rw [e, e2, mul_one]
  exact mul_mem r₁ h1

theorem refl_inv {W : Subgroup G} {x g : G} (hg : g ∈ normalizer (W : Set G)) (r : Refl W x g) :
    Refl W x g⁻¹ := by
  unfold Refl at *
  have h1 : g * (x * g * x⁻¹ * g)⁻¹ * g⁻¹ ∈ W := by
    have := (mem_normalizer_iff.1 hg ((x * g * x⁻¹ * g)⁻¹)).1 (inv_mem r)
    exact this
  have e : x * g⁻¹ * x⁻¹ * g⁻¹ = g * (x * g * x⁻¹ * g)⁻¹ * g⁻¹ := by group
  rw [e]
  exact h1

theorem refl_zpow {W : Subgroup G} {x g : G} (hg : g ∈ normalizer (W : Set G)) (r : Refl W x g) :
    ∀ n : ℤ, Refl W x (g ^ n) := by
  intro n
  induction n using Int.induction_on with
  | zero => simpa using refl_one W x
  | succ i ih =>
    rw [zpow_add_one]
    exact refl_mul (zpow_mem hg i) ((Commute.zpow_self g i).eq) ih r
  | pred i ih =>
    rw [zpow_sub_one]
    have hc : g ^ (-(i : ℤ)) * g⁻¹ = g⁻¹ * g ^ (-(i : ℤ)) :=
      ((Commute.zpow_self g (-(i : ℤ))).inv_right).eq
    exact refl_mul (zpow_mem hg _) hc ih (refl_inv hg r)

theorem mul_zpowers_comm {S W : Subgroup G} {x h : G} (hWS : W ≤ S) (hxS : x ∈ S)
    (hSW : ∀ s ∈ S, s ∈ W ∨ x⁻¹ * s ∈ W) (hh : h ∈ normalizer (W : Set G))
    (hrefl : ∀ n : ℤ, Refl W x (h ^ n)) :
    (S : Set G) * (zpowers h : Set G) = (zpowers h : Set G) * (S : Set G) := by
  have key : ∀ s ∈ S, ∀ n : ℤ, ∃ k : ℤ, ∃ s' ∈ S, s * h ^ n = h ^ k * s' := by
    intro s hs n
    have hg : h ^ n ∈ normalizer (W : Set G) := zpow_mem hh n
    rcases hSW s hs with hsW | hq
    · refine ⟨n, (h ^ n)⁻¹ * s * h ^ n, hWS ?_, by group⟩
      have := (mem_normalizer_iff.1 (inv_mem hg) s).1 hsW
      simpa using this
    · set q := x⁻¹ * s with hqdef
      have hs' : s = x * q := by rw [hqdef]; group
      have hr : x * h ^ n * x⁻¹ * h ^ n ∈ W := hrefl n
      have hq' : (h ^ n)⁻¹ * q * h ^ n ∈ W := by
        have := (mem_normalizer_iff.1 (inv_mem hg) q).1 hq
        simpa using this
      have hr' : h ^ n * (x * h ^ n * x⁻¹ * h ^ n) * (h ^ n)⁻¹ ∈ W := by
        have := (mem_normalizer_iff.1 hg _).1 hr
        exact this
      refine ⟨-n, (h ^ n * (x * h ^ n * x⁻¹ * h ^ n) * (h ^ n)⁻¹) * x * ((h ^ n)⁻¹ * q * h ^ n),
        mul_mem (mul_mem (hWS hr') hxS) (hWS hq'), ?_⟩
      rw [hs', zpow_neg]
      group
  ext y
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨s, hs, b, hb, rfl⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    obtain ⟨k, s', hs', e⟩ := key s hs n
    exact ⟨h ^ k, mem_zpowers_iff.2 ⟨k, rfl⟩, s', hs', e.symm⟩
  · rintro ⟨a, ha, s, hs, rfl⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨k, s', hs', e⟩ := key s⁻¹ (inv_mem hs) (-m)
    refine ⟨s'⁻¹, inv_mem hs', h ^ (-k), mem_zpowers_iff.2 ⟨-k, rfl⟩, ?_⟩
    have : (h ^ m * s)⁻¹ = h ^ k * s' := by
      rw [mul_inv_rev, ← zpow_neg]; exact e
    calc s'⁻¹ * h ^ (-k) = (h ^ k * s')⁻¹ := by rw [mul_inv_rev, zpow_neg]
      _ = h ^ m * s := by rw [← this]; simp

theorem exists_three_part [Finite G] (a : G) :
    ∃ m : ℕ, ¬ 3 ∣ m ∧ ∃ j : ℕ, orderOf (a ^ m) = 3 ^ j := by
  have hpos : 0 < orderOf a := orderOf_pos a
  have hmul : 3 ^ ((orderOf a).factorization 3) * (orderOf a / 3 ^ ((orderOf a).factorization 3)) =
      orderOf a := Nat.ordProj_mul_ordCompl_eq_self (orderOf a) 3
  have hcop : Nat.Coprime 3 (orderOf a / 3 ^ ((orderOf a).factorization 3)) :=
    Nat.coprime_ordCompl Nat.prime_three hpos.ne'
  set j := (orderOf a).factorization 3 with hj
  set m := orderOf a / 3 ^ j with hm
  refine ⟨m, fun h3 => ?_, j, ?_⟩
  · have := Nat.Coprime.eq_one_of_dvd hcop h3
    omega
  · have hmdvd : m ∣ orderOf a := Dvd.intro_left _ hmul
    have hm0 : m ≠ 0 := by
      intro h
      rw [h] at hmul
      omega
    rw [orderOf_pow_of_dvd hm0 hmdvd]
    conv_lhs => rw [← hmul]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
