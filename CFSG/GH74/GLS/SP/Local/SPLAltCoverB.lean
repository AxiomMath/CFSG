module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXCtx
public import CFSG.GH74.GLS.IVK.L2.Transport

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem altCover_l2Order_cases {q p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : q = p ^ f) (hodd : Odd q)
    (h5 : 5 ≤ q) (hdvd : q * (q ^ 2 - 1) / 2 ∣ 19958400) :
    q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 11 := by
  have hqN : q ∣ 19958400 := by
    obtain ⟨m, hm⟩ : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hodd.pow odd_one
    have hn : q * (q ^ 2 - 1) / 2 = q * m := by rw [hm, Nat.mul_add]; omega
    rw [hn] at hdvd
    exact (Dvd.intro m rfl).trans hdvd
  have hpN : p ∣ 19958400 := (hq ▸ dvd_pow_self p (by omega : f ≠ 0)).trans hqN
  have hp11 : p ≤ 11 := by
    have h1 : p ∣ Nat.factorial 11 := hpN.trans ⟨2, by decide⟩
    exact (hp.dvd_factorial).mp h1
  have hq341 : q ≤ 341 := by
    by_contra h
    push Not at h
    have h1 : 342 * (342 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    have h2 : q * (q ^ 2 - 1) / 2 ≤ 19958400 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [← hq] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) h2
  have hf5 : f ≤ 5 := by
    by_contra h
    push Not at h
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have : 3 ^ 6 ≤ p ^ f := (Nat.pow_le_pow_left h3 6).trans (Nat.pow_le_pow_right (by omega) h)
    omega
  subst hq
  revert hp hdvd hodd h5 hp2
  interval_cases p <;> interval_cases f <;> norm_num

theorem altCover_l2Order_not_dvd {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q) (hdvd : q * (q ^ 2 - 1) / 2 ∣ 2304) :
    False := by
  have hq : q ≤ 17 := by
    by_contra h
    push Not at h
    have h1 : 18 * (18 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    have h2 : q * (q ^ 2 - 1) / 2 ≤ 2304 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨k, rfl⟩ := hodd
  have hk8 : k ≤ 8 := by omega
  have hk2 : 2 ≤ k := by omega
  revert hdvd
  interval_cases k <;> norm_num

theorem altCover_center_eq_bot_of_isL2 {K : Type} [Group K] {P : ℕ → Prop} (h : IVK.IsL2 K P) :
    center K = ⊥ := by
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := h
  let e' : K ≃* GorensteinWalter.PSL2 F := IVK.toPSL e
  have hP : center (GorensteinWalter.PSL2 F) = ⊥ := GorensteinWalter.psl2_center_eq_bot F
  rw [eq_bot_iff]
  intro z hz
  have hz' : e' z ∈ center (GorensteinWalter.PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e'.surjective g
    have hk := Subgroup.mem_center_iff.1 hz k
    rw [← map_mul, ← map_mul, hk]
  rw [hP, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (e'.injective (by rw [hz', map_one]))

theorem XCtx.altCover_A_facts {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}
    (ctx : XCtx X z t A T₁) :
    ∃ q p f : ℕ, Odd q ∧ 5 ≤ q ∧ p.Prime ∧ 1 ≤ f ∧ q = p ^ f ∧
      Nat.card ↥A = q * (q ^ 2 - 1) / 2 ∧ center ↥A = ⊥ := by
  obtain ⟨q, hqodd, hq5, hAL2⟩ := ctx.A_L2
  have hAL2' := hAL2
  obtain ⟨F, _, _, hqF, ⟨e⟩⟩ := hAL2'
  have hqF : Nat.card F = q := hqF
  have hF : IVK.L2Field F := ⟨hqF ▸ hqodd, by omega⟩
  obtain ⟨p, f, hp, -, hf, hpf⟩ := IVK.isOddPrimePower_of_L2Field hF
  refine ⟨q, p, f, hqodd, hq5, hp, hf, hqF ▸ hpf, ?_, altCover_center_eq_bot_of_isL2 hAL2⟩
  rw [IVK.card_eq_of_L2Field e hF, hqF]

theorem altCover_eq_one_of_mem_center {X : Type} [Group X] {A L : Subgroup X} (hAL : A ≤ L)
    (hA : center ↥A = ⊥) {a : X} (ha : a ∈ A) (hc : (⟨a, hAL ha⟩ : ↥L) ∈ center ↥L) : a = 1 := by
  have h : (⟨a, ha⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨(g : X), hAL g.2⟩)
    exact Subtype.ext h2
  rw [hA, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem altCover_card_dvd_of_ker_le_center {X : Type} [Group X] {A L : Subgroup X} (hAL : A ≤ L)
    (hA : center ↥A = ⊥) {G' : Type} [Group G'] [Finite G'] (φ : ↥L →* G')
    (hφ : φ.ker ≤ center ↥L) : Nat.card ↥A ∣ Nat.card G' := by
  refine Subgroup.card_dvd_of_injective (φ.comp (Subgroup.inclusion hAL)) ?_
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : Subgroup.inclusion hAL a ∈ φ.ker := ha
  exact Subtype.ext (altCover_eq_one_of_mem_center hAL hA a.2 (hφ h1))

theorem XCtx.altCover_card_T₁_le_eight {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}
    (ctx : XCtx X z t A T₁) (hdvd : Nat.card ↥A ∣ 19958400) : Nat.card ↥T₁ ≤ 8 := by
  obtain ⟨q, p, f, hodd, h5, hp, hf, hq, hcard, -⟩ := ctx.altCover_A_facts
  rw [hcard] at hdvd
  have hq' := altCover_l2Order_cases hp hf hq hodd h5 hdvd
  obtain ⟨k, hk⟩ := ctx.T₁_pgrp.exists_card_eq
  have hT : Nat.card ↥T₁ ∣ Nat.card ↥A := Subgroup.card_dvd_of_le ctx.T₁_le
  rw [hk, hcard] at hT
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h16' := h16.trans hT
    rcases hq' with rfl | rfl | rfl | rfl <;> norm_num at h16'
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

theorem XCtx.altCover_card_le_one_two_eight {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}
    (ctx : XCtx X z t A T₁) (hdvd : Nat.card ↥A ∣ 19958400) {P : Subgroup X}
    (hP : IsPGroup 2 ↥P) : Nat.card ↥P ≤ 128 := by
  have h8 := ctx.altCover_card_T₁_le_eight hdvd
  have h := ctx.bound P hP
  have : Nat.card ↥T₁ ^ 2 ≤ 8 ^ 2 := Nat.pow_le_pow_left h8 2
  omega

theorem altCover_exists_twoSubgroup_of_pow_dvd {X : Type} [Group X] [Finite X] (M : Subgroup X) {k : ℕ}
    (h : 2 ^ k ∣ Nat.card ↥M) : ∃ P : Subgroup X, IsPGroup 2 ↥P ∧ 2 ^ k ≤ Nat.card ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  have hcard : Nat.card ↥((R : Subgroup ↥M).map M.subtype) = Nat.card ↥(R : Subgroup ↥M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  refine ⟨(R : Subgroup ↥M).map M.subtype, ?_, ?_⟩
  · exact IsPGroup.of_card (by rw [hcard]; exact R.card_eq_multiplicity)
  · rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos (R.pow_dvd_card_of_pow_dvd_card h)

end CFSG.GH74.GLS.SP.Local
