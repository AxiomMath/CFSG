module

public import CFSG.LocalAnalysis.GH72.G3aOdd

public section

namespace CFSG.GH72

open Subgroup

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem lemma_3_8 (𝔖 : Sec3Setting G) (h₁ : IsDihNonab 𝔖.S₁) :
    ∀ s ∈ (𝔖.S : Subgroup G), ∀ t ∈ (𝔖.S : Subgroup G),
      (𝔖.S : Subgroup G) ≤ C s → (𝔖.S : Subgroup G) ≤ C t → orderOf s = 2 → IsConj s t →
        s = t := by
  intro s hsS t htS hSs hSt hz2 hconj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 G) := 𝔖.S.finite_of_finiteIndex
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hs_cent_S : ∀ y ∈ (𝔖.S : Subgroup G), y * s = s * y := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSs hy)
  have ht_cent : t ∈ Subgroup.centralizer ((𝔖.S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSt hy)
  have hgts : g⁻¹ * t * g = s := by
    rw [← hg]
    group
  have hyc : g⁻¹ * t * g ∈ Subgroup.centralizer ((𝔖.S : Subgroup G) : Set G) := by
    rw [hgts]
    exact Subgroup.mem_centralizer_iff.mpr hs_cent_S
  obtain ⟨n, hnN, hnconj⟩ :=
    Sylow.conj_eq_normalizer_conj_of_mem_centralizer (𝔖.S) t g ht_cent hyc
  have hs_eq : s = n⁻¹ * t * n := by
    rw [← hgts]
    exact hnconj
  have ht_eq : t = n * s * n⁻¹ := by
    rw [hs_eq]
    group
  have mem_S_of_two : ∀ {x : G}, IsPGroup 2 (Subgroup.zpowers x) →
      x ∈ Subgroup.normalizer (𝔖.S : Set G) → x ∈ (𝔖.S : Subgroup G) := by
    intro x hx hxN
    have hxnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (𝔖.S : Set G) := by
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact zpow_mem hxN j
    have hinf := IsPGroup.inf_normalizer_sylow hx (𝔖.S)
    have hmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer (𝔖.S : Set G) :=
      ⟨Subgroup.mem_zpowers x, hxN⟩
    rw [hinf] at hmem
    exact hmem.2
  obtain ⟨k, r, hodd_r, hm_eq0⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  let e : ℕ := 2 ^ k
  have hm_eq : orderOf n = e * r := hm_eq0
  have hn₀_fix : ∀ {u : G}, Odd (orderOf u) →
      u ∈ Subgroup.normalizer (𝔖.S : Set G) → u * s * u⁻¹ = s := by
    intro u hu huN
    exact odd_fixes_central_involutions_of_dd (D := (𝔖.S : Subgroup G)) (D₁ := 𝔖.S₁)
      (D₂ := 𝔖.S₂) 𝔖.decomp h₁ hu huN hsS hs_cent_S hz2
  by_cases hr1 : r = 1
  ·
    have hndvd : orderOf n ∣ e := by
      rw [hm_eq, hr1, mul_one]
    have hPn : IsPGroup 2 (Subgroup.zpowers n) := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro y
      refine ⟨k, ?_⟩
      rw [← Subgroup.orderOf_coe y]
      exact (orderOf_dvd_of_mem_zpowers y.2).trans hndvd
    have hnS : n ∈ (𝔖.S : Subgroup G) := mem_S_of_two hPn hnN
    have hfix : n * s * n⁻¹ = s := by
      rw [hs_cent_S n hnS]
      group
    exact (ht_eq.trans hfix).symm
  ·
    have hr_gt_one : 1 < r := by
      have hpos : 0 < r := hodd_r.pos
      omega
    have he_coprime : Nat.Coprime e r :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd_r)
    obtain ⟨A, -, hA_mod⟩ :=
      Nat.exists_mul_mod_eq_one_of_coprime (n := e) (k := r) he_coprime hr_gt_one
    obtain ⟨q, hEA⟩ : ∃ q, e * A = r * q + 1 := by
      refine ⟨e * A / r, ?_⟩
      have h := Nat.div_add_mod (e * A) r
      omega
    let n₂ : G := ((n ^ r) ^ q)⁻¹
    let n₀ : G := (n ^ e) ^ A
    have hn₂_def : n₂ = ((n ^ r) ^ q)⁻¹ := rfl
    have hn₀_def : n₀ = (n ^ e) ^ A := rfl
    have hre : r * e = orderOf n := by
      rw [hm_eq]
      exact Nat.mul_comm r e
    have hn₂dvd : orderOf (n ^ r) ∣ e := by
      rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, hre, pow_orderOf_eq_one]
    have hn₀dvd : orderOf (n ^ e) ∣ r := by
      rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul]
      rw [← hm_eq, pow_orderOf_eq_one]
    have hn₂_ord : orderOf n₂ ∣ e := by
      rw [hn₂_def, orderOf_inv]
      exact (orderOf_pow_dvd (x := n ^ r) q).trans hn₂dvd
    have hn₀_ord : orderOf n₀ ∣ r := by
      rw [hn₀_def]
      exact (orderOf_pow_dvd (x := n ^ e) A).trans hn₀dvd
    have hn₂N : n₂ ∈ Subgroup.normalizer (𝔖.S : Set G) := by
      rw [hn₂_def]
      exact Subgroup.inv_mem _ (pow_mem (pow_mem hnN r) q)
    have hn₀N : n₀ ∈ Subgroup.normalizer (𝔖.S : Set G) := by
      rw [hn₀_def]
      exact pow_mem (pow_mem hnN e) A
    have hPn₂ : IsPGroup 2 (Subgroup.zpowers n₂) := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro y
      refine ⟨k, ?_⟩
      rw [← Subgroup.orderOf_coe y]
      exact (orderOf_dvd_of_mem_zpowers y.2).trans hn₂_ord
    have hn₂S : n₂ ∈ (𝔖.S : Subgroup G) := mem_S_of_two hPn₂ hn₂N
    have hn₂_fix : n₂ * s * n₂⁻¹ = s := by
      rw [hs_cent_S n₂ hn₂S]
      group
    have hn₀_fix' : n₀ * s * n₀⁻¹ = s :=
      hn₀_fix (hodd_r.of_dvd_nat hn₀_ord) hn₀N
    have hpow : (n ^ e) ^ A = (n ^ r) ^ q * n := by
      rw [← pow_mul, hEA, pow_succ, pow_mul]
    have hn_eq : n₂ * n₀ = n := by
      rw [hn₂_def, hn₀_def, hpow]
      group
    exact (calc t = n * s * n⁻¹ := ht_eq
      _ = (n₂ * n₀) * s * (n₂ * n₀)⁻¹ := by rw [hn_eq]
      _ = n₂ * (n₀ * s * n₀⁻¹) * n₂⁻¹ := by group
      _ = n₂ * s * n₂⁻¹ := by rw [hn₀_fix']
      _ = s := hn₂_fix).symm

end Sec3Setting

end CFSG.GH72
