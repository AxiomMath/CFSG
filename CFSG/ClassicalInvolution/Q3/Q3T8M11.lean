module

public import CFSG.ClassicalInvolution.Q3.Q3NMM11

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Blueprint CFSG.Sporadic.Mathieu Equiv CFSG.ClassicalInvolution.Q3
open scoped Pointwise

private theorem sd_check : ∀ p q : Fin 8 × Fin 2,
    m11SdMap p ^ 4 = 1 → m11SdMap p ^ 2 ≠ 1 → m11SdMap p * m11SdMap q = m11SdMap q * m11SdMap p →
      m11SdMap q ^ 4 = 1 → ∃ t : Fin 4, m11SdMap q = m11SdMap p ^ t.val := by
  decide +kernel

private theorem card_m11SdS_eq_sylow :
    Nat.card m11SdS = 2 ^ (Nat.card ↥NativeSporadic.M11).factorization 2 := by
  rw [card_m11SdS, card_m11_kernel]
  have hv : padicValNat 2 7920 = 4 := by
    have h : (7920 : ℕ) = 2 ^ 4 * 495 := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    have : padicValNat 2 495 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  have h2 : (7920 : ℕ).factorization 2 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    exact hv
  rw [h2]
  norm_num

theorem m11_mem_zpowers_of_commute {s k : ↥NativeSporadic.M11} (hs : orderOf s = 4)
    (hsk : s * k = k * s) (hk : k ^ 4 = 1) : k ∈ Subgroup.zpowers s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Sylow 2 ↥NativeSporadic.M11 := Sylow.ofCard m11SdS card_m11SdS_eq_sylow
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hs]; norm_num)
  have hkord : orderOf k ∣ 2 ^ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    simpa using hk
  have hk2 : IsPGroup 2 (Subgroup.zpowers k) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hkord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hc : ∀ x ∈ Subgroup.zpowers s, k * x * k⁻¹ = x := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hks : Commute k s := hsk.symm
    have hcm : Commute k (s ^ m) := hks.zpow_right m
    rw [hcm.eq]
    group
  have hc' : ∀ x ∈ Subgroup.zpowers s, k⁻¹ * x * k = x := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hks : Commute k s := hsk.symm
    have hcm : Commute k (s ^ m) := hks.zpow_right m
    have hcm' : Commute k⁻¹ (s ^ m) := hcm.inv_left
    rw [hcm'.eq]
    group
  have hnorm : Subgroup.zpowers k ≤ Subgroup.normalizer (Subgroup.zpowers s : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hc x hx]
      exact hx
    · intro hx
      have := hc' _ hx
      have e : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      rw [e] at this
      rw [this]
      exact hx
  have hA : IsPGroup 2 ↥(Subgroup.zpowers k ⊔ Subgroup.zpowers s) :=
    hk2.to_sup_of_normal_right' hs2 hnorm
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M11 P₀ Q
  have hsQ : s ∈ (Q : Subgroup ↥NativeSporadic.M11) :=
    hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hkQ : k ∈ (Q : Subgroup ↥NativeSporadic.M11) :=
    hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers k))
  have hsQ' : s ∈ MulAut.conj g • (m11SdS : Subgroup ↥NativeSporadic.M11) := by
    have h := hsQ
    rw [← hg, Sylow.coe_subgroup_smul] at h
    exact h
  have hkQ' : k ∈ MulAut.conj g • (m11SdS : Subgroup ↥NativeSporadic.M11) := by
    have h := hkQ
    rw [← hg, Sylow.coe_subgroup_smul] at h
    exact h
  have hconj : ∀ x : ↥NativeSporadic.M11, ((MulAut.conj g)⁻¹ • x : ↥NativeSporadic.M11) =
      g⁻¹ * x * g := by
    intro x
    simp [MulAut.smul_def, MulAut.conj_symm_apply]
  let c : ↥NativeSporadic.M11 ≃* ↥NativeSporadic.M11 := MulAut.conj g⁻¹
  have hcx : ∀ x : ↥NativeSporadic.M11, c x = g⁻¹ * x * g := by
    intro x
    simp [c]
  have hs' : c s ∈ m11SdS := by
    have h1 := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 hsQ'
    rwa [hconj, ← hcx] at h1
  have hk' : c k ∈ m11SdS := by
    have h1 := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 hkQ'
    rwa [hconj, ← hcx] at h1
  obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem hs'
  obtain ⟨q, hq⟩ := exists_m11SdMap_eq_of_mem hk'
  have hs4 : (c s) ^ 4 = 1 := by
    rw [← map_pow, show s ^ 4 = 1 by rw [← hs]; exact pow_orderOf_eq_one s, map_one]
  have hs2' : (c s) ^ 2 ≠ 1 := by
    intro h
    have h2 : s ^ 2 = 1 := by
      apply c.injective
      rw [map_pow, map_one]
      exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hs] at this
    omega
  have hk4 : (c k) ^ 4 = 1 := by
    rw [← map_pow, hk, map_one]
  have hcomm : (c s) * (c k) = (c k) * (c s) := by
    rw [← map_mul, ← map_mul, hsk]
  have hp4 : m11SdMap p ^ 4 = 1 := by
    rw [hp]
    have := congrArg Subtype.val hs4
    simpa using this
  have hp2 : m11SdMap p ^ 2 ≠ 1 := by
    rw [hp]
    intro h
    apply hs2'
    exact Subtype.ext (by simpa using h)
  have hq4 : m11SdMap q ^ 4 = 1 := by
    rw [hq]
    have := congrArg Subtype.val hk4
    simpa using this
  have hpq : m11SdMap p * m11SdMap q = m11SdMap q * m11SdMap p := by
    rw [hp, hq]
    exact congrArg Subtype.val hcomm
  obtain ⟨t, ht⟩ := sd_check p q hp4 hp2 hpq hq4
  have hkt : c k = (c s) ^ t.val := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow]
    rw [← hq, ht, hp]
  have hk_eq : k = s ^ t.val := by
    apply c.injective
    rw [hkt, map_pow]
  rw [hk_eq]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _

private theorem center_m11 : Subgroup.center ↥NativeSporadic.M11 = ⊥ := by
  have hs := (m11Facts).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥NativeSporadic.M11) with
    h | h
  · exact h
  · exfalso
    obtain ⟨x, y, -, hx8, -, hyx⟩ := exists_semidihedral_sylow
    have hxc : x ∈ Subgroup.center ↥NativeSporadic.M11 := by rw [h]; exact Subgroup.mem_top x
    have hcomm : y * x = x * y := (Subgroup.mem_center_iff.mp hxc y)
    have h3 : x ^ 3 = x := by
      rw [← hyx, hcomm]
      group
    have h2 : x ^ 2 = 1 := by
      have : x ^ 2 * x = 1 * x := by
        calc x ^ 2 * x = x ^ 3 := by group
          _ = x := h3
          _ = 1 * x := by group
      exact mul_right_cancel this
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx8] at this
    omega

private theorem zpow_two_mul_cases {Y : Type} [Group Y] {u : Y} (hu : u ^ 4 = 1) (j : ℤ) :
    u ^ (2 * j) = 1 ∨ u ^ (2 * j) = u ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
  have h4 : u ^ (4 : ℤ) = 1 := by exact_mod_cast hu
  have hmul : ∀ m : ℤ, u ^ (4 * m) = 1 := fun m => by rw [zpow_mul, h4, one_zpow]
  rcases hm with rfl | rfl
  · left
    rw [show 2 * (2 * m) = 4 * m by ring]
    exact hmul m
  · right
    rw [show 2 * (2 * m + 1) = 4 * m + 2 by ring, zpow_add, hmul m, one_mul]
    norm_cast

theorem m11_dich {Y : Type} [Group Y]
    (ψ : ↥NativeSporadic.M11 →* Y) (hsurj : Function.Surjective ψ) {s : ↥NativeSporadic.M11}
    (hs : orderOf (ψ s) = 4) (β : MulAut Y) (hβs : β (ψ s) = ψ s) (hβ : β ^ 4 = 1) :
    β ^ 2 = 1 ∨ β ^ 2 = MulAut.conj (ψ s ^ 2) := by
  classical
  have hsimple : IsSimpleGroup ↥NativeSporadic.M11 := (m11Facts).1
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hker : x ∈ ψ.ker := hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · rw [h] at hker
      exact Subgroup.mem_bot.mp hker
    · exfalso
      have h1 : ψ s = 1 := by
        have : s ∈ ψ.ker := by rw [h]; exact Subgroup.mem_top s
        exact this
      rw [h1, orderOf_one] at hs
      omega
  let e : ↥NativeSporadic.M11 ≃* Y := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have he : ∀ x, e x = ψ x := fun x => rfl
  obtain ⟨k, hk⟩ := Q3NM.m11_aut_inner (MulAut.congr e.symm β)
  have hβconj : β = MulAut.conj (ψ k) := by
    ext y
    have h1 : (MulAut.congr e.symm β) (e.symm y) = k * e.symm y * k⁻¹ := by
      rw [hk]; simp [MulAut.conj_apply]
    have h2 : (MulAut.congr e.symm β) (e.symm y) = e.symm (β y) := by
      simp [MulAut.congr_apply]
    have h3 : β y = e (k * e.symm y * k⁻¹) := by
      rw [← h1, h2]; simp
    rw [h3, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply, he]
  have hs4' : orderOf s = 4 := by rw [← hs]; exact (orderOf_injective ψ hinj s).symm
  have hsk : s * k = k * s := by
    have h1 := hβs
    rw [hβconj, MulAut.conj_apply] at h1
    have h2 : ψ k * ψ s = ψ s * ψ k := by
      calc ψ k * ψ s = (ψ k * ψ s * (ψ k)⁻¹) * ψ k := by group
        _ = ψ s * ψ k := by rw [h1]
    apply hinj
    rw [map_mul, map_mul]
    exact h2.symm
  have hk4 : k ^ 4 = 1 := by
    have h1 : MulAut.conj ((ψ k) ^ 4) = 1 := by
      rw [map_pow, ← hβconj]; exact hβ
    have hcen : k ^ 4 ∈ Subgroup.center ↥NativeSporadic.M11 := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply hinj
      have h2 := DFunLike.congr_fun h1 (ψ x)
      rw [MulAut.conj_apply] at h2
      simp only [MulAut.one_apply] at h2
      rw [map_mul, map_mul, map_pow]
      have h3 : (ψ k) ^ 4 * ψ x = ψ x * (ψ k) ^ 4 := by
        calc (ψ k) ^ 4 * ψ x = ((ψ k) ^ 4 * ψ x * ((ψ k) ^ 4)⁻¹) * (ψ k) ^ 4 := by group
          _ = ψ x * (ψ k) ^ 4 := by rw [h2]
      exact h3.symm
    rw [center_m11, Subgroup.mem_bot] at hcen
    exact hcen
  have hkz : k ∈ Subgroup.zpowers s := m11_mem_zpowers_of_commute hs4' hsk hk4
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkz
  have hψk : ψ k = (ψ s) ^ j := by rw [← hj, map_zpow]
  have hu4 : (ψ s) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (ψ s)
    rwa [hs] at this
  have hpow : (ψ s ^ j) ^ 2 = (ψ s) ^ (2 * j) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    norm_cast
  have hβ2 : β ^ 2 = MulAut.conj ((ψ s) ^ (2 * j)) := by
    rw [hβconj, ← map_pow, hψk, hpow]
  rcases zpow_two_mul_cases hu4 j with h | h
  · left
    rw [hβ2, h, map_one]
  · right
    rw [hβ2, h]

end CFSG.ClassicalInvolution.Q3.Q3T8
