module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG.GH74.GLS.Stage1.Thm3

section Pure

variable {C : Type*} [Group C] [Finite C]

theorem eq_one_of_pow_two_pow_of_odd {D : Type*} [Group D] [Finite D] (hD : Odd (Nat.card D)) {x : D}
    {m : ℕ} (hx : x ^ (2 ^ m) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card D := orderOf_dvd_natCard x
  have h3 : Nat.Coprime (2 ^ m) (Nat.card D) :=
    Nat.Coprime.pow_left m ((Nat.coprime_two_left).2 hD)
  have h4 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact orderOf_eq_one_iff.1 h4

omit [Finite C] in
theorem inf_eq_bot_of_odd {S N : Subgroup C} (hS : IsPGroup 2 ↥S) (hN : Odd (Nat.card N)) :
    S ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxN⟩
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have hk' : x ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.coprime_two_left).2 hN)
  have h4 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact orderOf_eq_one_iff.1 h4

theorem mem_of_mem_sup_odd {K N : Subgroup C} [K.Normal] (hN : Odd (Nat.card N)) {u : C} {m : ℕ}
    (hu : u ^ (2 ^ m) = 1) (huKN : u ∈ K ⊔ N) : u ∈ K := by
  let φ : C →* C ⧸ K := QuotientGroup.mk' K
  have h1 : φ u ∈ (K ⊔ N).map φ := Subgroup.mem_map_of_mem φ huKN
  have hK : K.map φ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    simpa [φ] using hk
  have h2 : (K ⊔ N).map φ = N.map φ := by
    rw [Subgroup.map_sup, hK, bot_sup_eq]
  rw [h2] at h1
  have hodd : Odd (Nat.card (N.map φ)) := Odd.of_dvd_nat hN (Subgroup.card_map_dvd _ _)
  have hpow : (⟨φ u, h1⟩ : N.map φ) ^ (2 ^ m) = 1 := by
    apply Subtype.ext
    simp [← map_pow, hu]
  have hone := eq_one_of_pow_two_pow_of_odd hodd hpow
  have hφ : φ u = 1 := congrArg Subtype.val hone
  exact (QuotientGroup.eq_one_iff u).1 hφ

omit [Finite C] in
theorem exists_involution_lift {D : Type*} [Group D] (π : C →* D) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) {h : D} (hh : orderOf h = 2) : ∃ u : C, orderOf u = 2 ∧ π u = h := by
  obtain ⟨c, rfl⟩ := hπ h
  have hh2 : (π c) ^ 2 = 1 := by rw [← hh]; exact pow_orderOf_eq_one _
  have hc2 : c ^ 2 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hh2
  set k := orderOf (c ^ 2) with hk
  have hkd : k ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨c ^ 2, hc2⟩ : π.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hkodd : Odd k := Odd.of_dvd_nat hker hkd
  have hne : π c ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hh; omega
  have hpk : (π c) ^ k = π c := by
    obtain ⟨j, hj⟩ := hkodd
    rw [hj, pow_succ, pow_mul, hh2, one_pow, one_mul]
  refine ⟨c ^ k, ?_, by rw [map_pow, hpk]⟩
  have hsq : (c ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; exact pow_orderOf_eq_one _
  have hne' : c ^ k ≠ 1 := by
    intro h1
    have := congrArg π h1
    rw [map_pow, hpk, map_one] at this
    exact hne this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hsq hne'

omit [Finite C] in
theorem eq_of_mem_zpowers_of_orderOf_two {u x : C} (hu : orderOf u = 2) (hx : x ∈ zpowers u)
    (hx2 : orderOf x = 2) : x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hk : u ^ (k % 2) = u ^ k := by
    have := zpow_mod_orderOf u k
    rw [hu] at this
    push_cast at this
    exact this
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk
    rw [← hk, orderOf_one] at hx2
    omega
  · rw [h1, zpow_one] at hk
    exact hk.symm

theorem isConj_of_mem_coset {N : Subgroup C} [N.Normal] (hN : Odd (Nat.card N)) {u v : C}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u⁻¹ * v ∈ N) : IsConj u v := by
  set H := N ⊔ zpowers u with hH
  have hvH : v ∈ H := by
    have h1 : u ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have h2 : u⁻¹ * v ∈ H := Subgroup.mem_sup_left huv
    have := mul_mem h1 h2
    simpa using this
  have key : ∀ w ∈ H, orderOf w = 2 →
      (zpowers w).relIndex H * 2 = Nat.card H := by
    intro w hwH hw
    have := Subgroup.relIndex_mul_card (zpowers w) H
    rwa [inf_eq_left.2 ((Subgroup.zpowers_le).2 hwH), Nat.card_zpowers, hw] at this
  have huH : u ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hodd : Odd ((zpowers u).relIndex H) := by
    rw [hH, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N (zpowers u)]
    exact Odd.of_dvd_nat hN (Subgroup.relIndex_dvd_card _ _)
  have hsyl : ∀ w ∈ H, orderOf w = 2 → Sec4.M.Syl2In (zpowers w) H := by
    intro w hwH hw
    refine ⟨(Subgroup.zpowers_le).2 hwH, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw]; norm_num)
    · have h1 := key w hwH hw
      have h2 := key u huH hu
      have h3 : (zpowers w).relIndex H = (zpowers u).relIndex H := by omega
      rw [h3]
      exact (Nat.not_even_iff_odd.2 hodd) ∘ even_iff_two_dvd.2
  obtain ⟨c, hcH, hc⟩ := Sec4.M.Syl2In.exists_conj (hsyl u huH hu) (hsyl v hvH hv)
  have hv' : v ∈ zpowers v := Subgroup.mem_zpowers v
  rw [hc, Sec4.M.mem_cj] at hv'
  have hord : orderOf (c * v * c⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective v
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this]; exact hv
  have := eq_of_mem_zpowers_of_orderOf_two hu hv' hord
  exact (isConj_iff.2 ⟨c, this⟩).symm

end Pure

end CFSG.GH74.GLS.Stage1.Thm4
