module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def fixingAut (E : Subgroup G) : Subgroup (MulAut G) where
  carrier := {h | ∀ e ∈ E, h e = e}
  mul_mem' := by
    intro a b ha hb e he
    rw [MulAut.mul_apply, hb e he, ha e he]
  one_mem' := fun e _ => rfl
  inv_mem' := by
    intro a ha e he
    show a.symm e = e
    conv_lhs => rw [← ha e he]
    exact a.symm_apply_apply e

variable [Finite G]

theorem exists_conj_of_fixing {A : Type} [Group A] (Θ : MulAut G →* A)
    (hker : ∀ φ : MulAut G, Θ φ = 1 ↔ φ ∈ (MulAut.conj : G →* MulAut G).range)
    (hZ : center G = ⊥) {Φ β : MulAut G} (hΦ : orderOf (Θ Φ) = 3) (hΦ3 : Φ ^ 3 = 1)
    (g : G) (hg : β = MulAut.conj g * Φ) (hβ3 : β ^ 3 = 1) (E : Subgroup G)
    (hEΦ : ∀ e ∈ E, Φ e = e) (hEβ : ∀ e ∈ E, β e = e)
    (hcent : ∀ y : G, (∀ e ∈ E, y * e = e * y) → y ^ 3 = 1 → y = 1) :
    ∃ (y : G) (k : ℕ), (k = 1 ∨ k = 2) ∧
      β = MulAut.conj y * Φ ^ k * (MulAut.conj y)⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΘconj : ∀ y : G, Θ (MulAut.conj y) = 1 := fun y => (hker _).2 ⟨y, rfl⟩
  have hΘβ : Θ β = Θ Φ := by rw [hg, map_mul, hΘconj, one_mul]
  have hΦ1 : Φ ≠ 1 := by
    intro h
    rw [h, map_one, orderOf_one] at hΦ
    exact absurd hΦ (by norm_num)
  have hΦord : orderOf Φ = 3 := orderOf_eq_prime hΦ3 hΦ1
  have hβ1 : β ≠ 1 := by
    intro h
    rw [h, map_one] at hΘβ
    rw [← hΘβ, orderOf_one] at hΦ
    exact absurd hΦ (by norm_num)
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  set H0 : Subgroup (MulAut G) := (Subgroup.zpowers (Θ Φ)).comap Θ with hH0
  set F : Subgroup (MulAut G) := H0 ⊓ fixingAut E with hF
  have hΦF : Φ ∈ F :=
    ⟨Subgroup.mem_zpowers (Θ Φ), fun e he => hEΦ e he⟩
  have hβF : β ∈ F := ⟨by
    show Θ β ∈ Subgroup.zpowers (Θ Φ)
    rw [hΘβ]
    exact Subgroup.mem_zpowers _, fun e he => hEβ e he⟩
  let θ : F →* A := Θ.comp F.subtype
  have hcard : Nat.card θ.ker * Nat.card θ.range = Nat.card F := by
    rw [← Subgroup.card_mul_index θ.ker, Subgroup.index_ker]
  have hrange : Nat.card θ.range ∣ 3 := by
    have hle : θ.range ≤ Subgroup.zpowers (Θ Φ) := by
      rintro _ ⟨x, rfl⟩
      exact x.2.1
    rw [← hΦ, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hker3 : ¬ 3 ∣ Nat.card θ.ker := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    set h : MulAut G := ((x : F) : MulAut G) with hh
    have hΘh : Θ h = 1 := x.2
    obtain ⟨y, hy⟩ := (hker h).1 hΘh
    have hfix : ∀ e ∈ E, h e = e := (x : F).2.2
    have hyE : ∀ e ∈ E, y * e = e * y := by
      intro e he
      have := hfix e he
      rw [← hy, MulAut.conj_apply] at this
      calc y * e = (y * e * y⁻¹) * y := by group
        _ = e * y := by rw [this]
    have hord : orderOf h = 3 := by
      have : orderOf x = orderOf ((x : F) : MulAut G) := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      rw [hh]
      rw [← this, hx]
    have hh3 : h ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one h
    have hy3 : y ^ 3 = 1 := by
      have h1 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, hy]; exact hh3
      have h2 : y ^ 3 ∈ center G := by
        rw [Subgroup.mem_center_iff]
        intro w
        have := congrArg (fun φ : MulAut G => φ w) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc w * y ^ 3 = (y ^ 3 * w * (y ^ 3)⁻¹) * y ^ 3 := by rw [this]
          _ = y ^ 3 * w := by group
      rw [hZ, Subgroup.mem_bot] at h2
      exact h2
    have hy1 := hcent y hyE hy3
    rw [hy1, map_one] at hy
    rw [← hy, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have h3F : 3 ∣ Nat.card F := by
    rw [← hΦord]
    exact (Subgroup.orderOf_mk Φ hΦF).symm ▸ orderOf_dvd_natCard (⟨Φ, hΦF⟩ : F)
  have hfac : (Nat.card F).factorization 3 = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hrange with h1 | h3
    · exfalso
      rw [h1, mul_one] at hcard
      rw [← hcard] at h3F
      exact hker3 h3F
    · rw [← hcard, h3, Nat.factorization_mul (Nat.card_pos (α := θ.ker)).ne' (by norm_num),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hker3,
        Nat.Prime.factorization_self Nat.prime_three, zero_add]
  let Φ' : F := ⟨Φ, hΦF⟩
  let β' : F := ⟨β, hβF⟩
  have hΦ'ord : orderOf Φ' = 3 := by rw [← hΦord]; exact Subgroup.orderOf_mk Φ hΦF
  have hβ'ord : orderOf β' = 3 := by rw [← hβord]; exact Subgroup.orderOf_mk β hβF
  let P : Sylow 3 F := Sylow.ofCard (Subgroup.zpowers Φ') (by
    rw [Nat.card_zpowers, hΦ'ord, hfac]; norm_num)
  let Q : Sylow 3 F := Sylow.ofCard (Subgroup.zpowers β') (by
    rw [Nat.card_zpowers, hβ'ord, hfac]; norm_num)
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq F P Q
  have hβQ : β' ∈ (Q : Subgroup F) := Subgroup.mem_zpowers β'
  have hQ : (Q : Subgroup F) = MulAut.conj w • (P : Subgroup F) := by
    rw [← hw, Sylow.coe_subgroup_smul]
  rw [hQ, Subgroup.mem_smul_pointwise_iff_exists] at hβQ
  obtain ⟨s, hs, hsβ⟩ := hβQ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hs
  have hβeq : β' = w * Φ' ^ k * w⁻¹ := by
    rw [← hsβ, MulAut.smul_def, MulAut.conj_apply, ← hk]
  have hkmod : Φ' ^ k = Φ' ^ (k % 3) := by
    have h := zpow_mod_orderOf Φ' k
    rw [hΦ'ord] at h
    exact_mod_cast h.symm
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by
    have h0 : k % 3 ≠ 0 := by
      intro h0
      rw [h0, zpow_zero] at hkmod
      apply hβ1
      have : β' = 1 := by rw [hβeq, hkmod]; group
      exact congrArg Subtype.val this
    omega
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 w.2.1
  have hΘw : Θ ((w : F) : MulAut G) = Θ (Φ ^ j) := by rw [map_zpow]; exact hj.symm
  have hwj : ∃ y : G, ((w : F) : MulAut G) = MulAut.conj y * Φ ^ j := by
    have h1 : Θ (((w : F) : MulAut G) * (Φ ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, hΘw, mul_inv_cancel]
    obtain ⟨y, hy⟩ := (hker _).1 h1
    refine ⟨y, ?_⟩
    rw [hy]
    group
  obtain ⟨y, hy⟩ := hwj
  have hβmain : β = ((w : F) : MulAut G) * Φ ^ k * ((w : F) : MulAut G)⁻¹ :=
    congrArg Subtype.val hβeq
  rw [hy] at hβmain
  refine ⟨y, (k % 3).toNat, ?_, ?_⟩
  · omega
  · have hk' : Φ ^ k = Φ ^ ((k % 3).toNat) := by
      have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
      have h1 : ((k % 3).toNat : ℤ) = k % 3 := Int.toNat_of_nonneg h0
      have h2 : Φ ^ (k % 3) = Φ ^ k := by
        have := zpow_mod_orderOf Φ k
        rwa [hΦord, Nat.cast_ofNat] at this
      rw [← h2, ← zpow_natCast, h1]
    rw [hβmain, hk']
    have hc : Commute (Φ ^ j) (Φ ^ ((k % 3).toNat)) := by
      rw [← zpow_natCast]
      exact (Commute.refl Φ).zpow_zpow j _
    calc MulAut.conj y * Φ ^ j * Φ ^ (k % 3).toNat * (MulAut.conj y * Φ ^ j)⁻¹
        = MulAut.conj y * (Φ ^ j * Φ ^ (k % 3).toNat * (Φ ^ j)⁻¹) * (MulAut.conj y)⁻¹ := by group
      _ = MulAut.conj y * Φ ^ (k % 3).toNat * (MulAut.conj y)⁻¹ := by
        rw [hc.eq, mul_inv_cancel_right]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
