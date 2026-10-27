module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Sound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallCore
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

theorem noQ16_of_not_dvd_card {G : Type*} [Group G] [Finite G] (h : ¬ 16 ∣ Nat.card G) :
    NoQ16 G := by
  intro x y hxy
  obtain ⟨hx4, hx8, hy2, hyx⟩ := hxy
  have hxo : orderOf x = 8 := by
    have hd : orderOf x ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one hx8
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have : j = 3 := by
      by_contra hne
      have hj3 : j ≤ 2 := by omega
      apply hx4
      have : orderOf x ∣ 4 := by
        rw [hj']
        calc 2 ^ j ∣ 2 ^ 2 := pow_dvd_pow 2 hj3
          _ = 4 := by norm_num
      exact orderOf_dvd_iff_pow_eq_one.mp this
    rw [hj', this]
    norm_num
  set H : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hH
  have hHp : IsPGroup 2 ↥H := isPGroup_sup_of_q16Pair ⟨hx4, hx8, hy2, hyx⟩
  have hxH : Subgroup.zpowers x ≤ H := le_sup_left
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hc8 : Nat.card (Subgroup.zpowers x) = 8 := by rw [Nat.card_zpowers, hxo]
  have hdvd : 8 ∣ Nat.card H := hc8 ▸ Subgroup.card_dvd_of_le hxH
  have hyx' : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    apply hx4
    have h1 : x ^ i * x * (x ^ i)⁻¹ = x := by
      rw [(Commute.zpow_left (Commute.refl x) i).eq, mul_inv_cancel_right]
    have h2 : x = x⁻¹ := h1.symm.trans hyx
    have h3 : x * x = 1 := by
      calc x * x = x⁻¹ * x := congrArg (· * x) h2
        _ = 1 := inv_mul_cancel x
    rw [show x ^ 4 = (x * x) * (x * x) by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two], h3]
    simp
  obtain ⟨k, hk⟩ := hHp.exists_card_eq
  have hne : Nat.card H ≠ 8 := by
    intro h8
    have := Subgroup.eq_of_le_of_card_ge hxH (by omega)
    exact hyx' (this ▸ hyH)
  have hk3 : 3 ≤ k := by
    have : 2 ^ 3 ∣ 2 ^ k := by rw [← hk]; exact hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : k = 3 := by omega
    exact hne (by rw [hk, this]; norm_num)
  apply h
  calc 16 = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ k := pow_dvd_pow 2 hk4
    _ = Nat.card H := hk.symm
    _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H

theorem conj_injective_of_center_eq_bot {F : Type*} [Group F] (hZ : Subgroup.center F = ⊥) :
    Function.Injective (MulAut.conj : F →* MulAut F) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut F => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = (g * x * g⁻¹) * g := by rw [this]
      _ = g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem center_eq_bot_of_simple {F : Type*} [Group F] [IsSimpleGroup F]
    (h : ∃ a b : F, a * b ≠ b * a) : Subgroup.center F = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h' | h'
  · exact h'
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center F := h' ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem noQ16_mulAut_of_odd_outer {F : Type} [Group F] (hZ : Subgroup.center F = ⊥)
    (hodd : Odd (Nat.card (Outer F))) (h : NoQ16 F) : NoQ16 (MulAut F) := by
  intro x y hxy
  have hinner : ∀ z : MulAut F, z ^ 8 = 1 → ∃ a : F, MulAut.conj a = z := by
    intro z hz
    have h1 : (QuotientGroup.mk z : Outer F) ^ 8 = 1 := by
      rw [← QuotientGroup.mk_pow, hz, QuotientGroup.mk_one]
    have h2 : orderOf (QuotientGroup.mk z : Outer F) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (QuotientGroup.mk z : Outer F) ∣ Nat.card (Outer F) := orderOf_dvd_natCard _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hj0 : j = 0 := by
      by_contra hj0
      have : 2 ∣ Nat.card (Outer F) := by
        refine Dvd.dvd.trans ?_ h3
        rw [hj]
        exact dvd_pow_self 2 hj0
      exact (Nat.not_even_iff_odd.mpr hodd) ((even_iff_two_dvd).mpr this)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact (QuotientGroup.eq_one_iff z).mp hj
  obtain ⟨hx4, hx8, hy2, hyx⟩ := hxy
  have hy8 : y ^ 8 = 1 := by
    calc y ^ 8 = (y ^ 2) ^ 4 := by rw [← pow_mul]
      _ = (x ^ 4) ^ 4 := by rw [hy2]
      _ = (x ^ 8) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hx8, one_pow]
  obtain ⟨a, rfl⟩ := hinner x hx8
  obtain ⟨b, rfl⟩ := hinner y hy8
  exact h a b (Q16Pair.of_map MulAut.conj (conj_injective_of_center_eq_bot hZ)
    ⟨hx4, hx8, hy2, hyx⟩)

theorem noQ16_mulAut_of_equiv {F G : Type*} [Group F] [Group G] (e : F ≃* G)
    (h : NoQ16 (MulAut G)) : NoQ16 (MulAut F) :=
  NoQ16.of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective h

theorem noQ16_mulAut_of_bijective_conj {F : Type*} [Group F] [Finite F]
    (hZ : Subgroup.center F = ⊥) (hsurj : ∀ φ : MulAut F, ∃ g : F, φ = MulAut.conj g)
    (hc : ¬ 16 ∣ Nat.card F) : NoQ16 (MulAut F) := by
  have hb : Function.Bijective (MulAut.conj : F →* MulAut F) :=
    ⟨conj_injective_of_center_eq_bot hZ, fun φ => by
      obtain ⟨g, hg⟩ := hsurj φ
      exact ⟨g, hg.symm⟩⟩
  exact NoQ16.of_injective (MulEquiv.ofBijective (MulAut.conj : F →* MulAut F) hb).symm.toMonoidHom
    (MulEquiv.ofBijective (MulAut.conj : F →* MulAut F) hb).symm.injective
    (noQ16_of_not_dvd_card hc)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
