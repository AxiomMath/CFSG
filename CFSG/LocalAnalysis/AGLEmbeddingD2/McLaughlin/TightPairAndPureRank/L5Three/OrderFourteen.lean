module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Regular
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem involution_two_fixed (hV : finrank (ZMod 2) V = 3) {t : V ≃ₗ[ZMod 2] V} (ht : t ^ 2 = 1) :
    ∃ u w : V, u ≠ 0 ∧ w ≠ 0 ∧ u ≠ w ∧ t u = u ∧ t w = w := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set φ : V →ₗ[ZMod 2] V := (t : V →ₗ[ZMod 2] V) - LinearMap.id with hφ
  have hφ2 : ∀ u, φ (φ u) = 0 := by
    intro u
    have h1 : t (t u) = u := by
      have := congrArg (fun g : V ≃ₗ[ZMod 2] V => g u) ht
      simpa [pow_two] using this
    simp only [hφ, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub, h1]
    have h3 := add_self_vec (t u)
    have h4 := add_self_vec u
    have : u - t u - (t u - u) = (u + u) - (t u + t u) := by abel
    rw [this, h3, h4]; simp
  have hle : LinearMap.range φ ≤ LinearMap.ker φ := by
    rintro _ ⟨u, rfl⟩
    exact hφ2 u
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hfin := Submodule.finrank_mono hle
  have hker : 2 ≤ finrank (ZMod 2) (LinearMap.ker φ) := by omega
  have hcard : 4 ≤ Nat.card (LinearMap.ker φ) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ finrank (ZMod 2) (LinearMap.ker φ) := Nat.pow_le_pow_right (by norm_num) hker
  have hS : 2 < ((LinearMap.ker φ : Set V) \ {0}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem (by simp)]
    have hk : ((LinearMap.ker φ : Set V)).ncard = Nat.card (LinearMap.ker φ) :=
      (Nat.card_coe_set_eq _).symm
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 hS
  have hfix : ∀ u : V, u ∈ (LinearMap.ker φ : Set V) \ {0} → t u = u ∧ u ≠ 0 := by
    rintro u ⟨hu, hu0⟩
    refine ⟨?_, by simpa using hu0⟩
    have : φ u = 0 := hu
    simp only [hφ, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this
    exact sub_eq_zero.1 this
  exact ⟨a, b, (hfix a ha).2, (hfix b hb).2, hab, (hfix a ha).1, (hfix b hb).1⟩

theorem zpow_fix_iff {q : ℕ} [Fact q.Prime] (hV : Nat.card V = q + 1) {x : V ≃ₗ[ZMod 2] V}
    (hx : orderOf x = q) {v : V} (hv : v ≠ 0) {m : ℤ} (hm : (x ^ m) v = v) : (q : ℤ) ∣ m := by
  have h1 : x ^ (m % (q : ℤ)) = x ^ m := by
    have := zpow_mod_orderOf x m
    rwa [hx] at this
  have hr0 : 0 ≤ m % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
  have h2 : (x ^ (m % (q : ℤ)).toNat) v = v := by
    have : x ^ (m % (q : ℤ)).toNat = x ^ m := by
      rw [← h1, ← zpow_natCast, Int.toNat_of_nonneg hr0]
    rw [this]; exact hm
  have h3 := pow_fix_iff hV hx hv h2
  have h4 : (q : ℤ) ∣ m % (q : ℤ) := by
    have := Int.natCast_dvd_natCast.2 h3
    rwa [Int.toNat_of_nonneg hr0] at this
  have h5 := Int.emod_add_mul_ediv m (q : ℤ)
  rw [← h5]
  exact dvd_add h4 (dvd_mul_right _ _)

theorem no_subgroup_fourteen (hV : finrank (ZMod 2) V = 3) (Y : Subgroup (V ≃ₗ[ZMod 2] V))
    (hY : Nat.card Y = 14) : False := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hVc : Nat.card V = 7 + 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV]; norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 7 (by rw [hY]; norm_num)
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 (by rw [hY]; norm_num)
  set x : V ≃ₗ[ZMod 2] V := (x₀ : V ≃ₗ[ZMod 2] V) with hxdef
  set t : V ≃ₗ[ZMod 2] V := (t₀ : V ≃ₗ[ZMod 2] V) with htdef
  have hx : orderOf x = 7 := (Subgroup.orderOf_coe x₀).trans hx₀
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t₀).trans ht₀
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have hidx : (Subgroup.zpowers x₀).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x₀)
    rw [Nat.card_zpowers, hx₀, hY] at this
    omega
  have : (Subgroup.zpowers x₀).Normal := Subgroup.normal_of_index_eq_two hidx
  have hconj : t₀ * x₀ * t₀⁻¹ ∈ Subgroup.zpowers x₀ :=
    Subgroup.Normal.conj_mem inferInstance x₀ (Subgroup.mem_zpowers x₀) t₀
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hconj
  have hj' : x ^ j = t * x * t⁻¹ := by
    have := congrArg (fun g : Y => (g : V ≃ₗ[ZMod 2] V)) hj
    simpa using this
  obtain ⟨v0, hv0⟩ : ∃ v0 : V, v0 ≠ 0 := by
    have : 0 < finrank (ZMod 2) V := by omega
    exact Module.finrank_pos_iff_exists_ne_zero.1 this
  have htne : ∀ u : V, u ≠ 0 → t u ≠ 0 := fun u hu h => hu (by
    have := congrArg (fun w => t⁻¹ w) h
    simpa using this)
  obtain ⟨c, -, hc⟩ := regular_action hVc hx hv0 (htne v0 hv0)
  have hact : ∀ k : ℕ, t ((x ^ k) v0) = (x ^ (j * k + c)) v0 := by
    intro k
    have h1 : t * x ^ k = x ^ (j * k) * t := by
      have h0 : (t * x * t⁻¹) ^ k = t * x ^ k * t⁻¹ := conj_pow
      rw [← hj', ← zpow_natCast, ← zpow_mul] at h0
      have : t * x ^ k = (x ^ (j * (k : ℤ))) * t := by
        calc t * x ^ k = (t * x ^ k * t⁻¹) * t := by group
          _ = x ^ (j * (k : ℤ)) * t := by rw [← h0]
      simpa using this
    calc t ((x ^ k) v0) = (t * x ^ k) v0 := rfl
      _ = (x ^ (j * k) * t) v0 := by rw [h1]
      _ = (x ^ (j * k)) (t v0) := rfl
      _ = (x ^ (j * k)) ((x ^ c) v0) := by rw [hc]
      _ = (x ^ (j * k) * x ^ (c : ℤ)) v0 := by simp
      _ = (x ^ (j * k + c)) v0 := by rw [← zpow_add]
  obtain ⟨u, w, hu0, hw0, huw, htu, htw⟩ := involution_two_fixed hV ht2
  obtain ⟨k1, hk1, hu⟩ := regular_action hVc hx hv0 hu0
  obtain ⟨k2, hk2, hw⟩ := regular_action hVc hx hv0 hw0
  have hk12 : k1 ≠ k2 := fun h => huw (by rw [← hu, ← hw, h])
  have hdiv : ∀ k : ℕ, t ((x ^ k) v0) = (x ^ k) v0 → (7 : ℤ) ∣ (j - 1) * k + c := by
    intro k hk
    rw [hact] at hk
    have hm : (x ^ ((j - 1) * k + c)) v0 = v0 := by
      have e : x ^ ((j - 1) * (k : ℤ) + c) = (x ^ (k : ℤ))⁻¹ * x ^ (j * k + c) := by
        rw [← zpow_neg, ← zpow_add]; congr 1; ring
      rw [e]
      show ((x ^ (k : ℤ))⁻¹) ((x ^ (j * k + c)) v0) = v0
      rw [hk]
      simp
    have := zpow_fix_iff hVc hx hv0 hm
    exact_mod_cast this
  have d1 := hdiv k1 (by rw [hu]; exact htu)
  have d2 := hdiv k2 (by rw [hw]; exact htw)
  have hp7 : Prime (7 : ℤ) := Int.prime_iff_natAbs_prime.2 (by norm_num)
  have hj1 : (7 : ℤ) ∣ j - 1 := by
    have h1 : (7 : ℤ) ∣ (j - 1) * ((k1 : ℤ) - k2) := by
      have := dvd_sub d1 d2
      convert this using 1; ring
    rcases hp7.dvd_or_dvd h1 with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := h
      omega
  have hc7 : (7 : ℤ) ∣ c := by
    have h1 : (7 : ℤ) ∣ (j - 1) * k1 := Dvd.dvd.mul_right hj1 _
    exact (dvd_add_right h1).1 d1
  have hone : t = 1 := by
    apply LinearEquiv.ext
    intro w
    by_cases hw0 : w = 0
    · simp [hw0]
    obtain ⟨k, -, hk⟩ := regular_action hVc hx hv0 hw0
    rw [← hk, hact]
    have h7 : (7 : ℤ) ∣ (j - 1) * k + c := dvd_add (Dvd.dvd.mul_right hj1 _) hc7
    have hone : x ^ ((j - 1) * (k : ℤ) + c) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hx]; exact_mod_cast h7
    have e : x ^ (j * k + c) = x ^ (k : ℤ) * x ^ ((j - 1) * (k : ℤ) + c) := by
      rw [← zpow_add]; congr 1; ring
    rw [e, hone, mul_one]
    simp
  rw [hone, orderOf_one] at ht
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
