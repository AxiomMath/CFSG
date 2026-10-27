module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core3

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

theorem O2In_normalizer_R (c : Core3 E t z) :
    TwoFi22.O2In (normalizer (Rg t z : Set G)) = Rg t z := by
  let X : Subgroup G := normalizer (Rg t z : Set G)
  change TwoFi22.O2In X = Rg t z
  have hR_le_X : Rg t z ≤ X := Subgroup.le_normalizer
  have hRsub_normal : ((Rg t z).subgroupOf X).Normal := Subgroup.normal_in_normalizer
  have hR2 : IsPGroup 2 (Rg t z) := IsPGroup.of_card (n := 13) c.jr.card_R
  have hR_le_O : Rg t z ≤ TwoFi22.O2In X := TwoB.le_O2In hR_le_X hRsub_normal hR2
  have hCNz_le_X : CNz E z ≤ X := by
    intro n hn
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact c.rnorm n hn x hx
    · intro hx
      have h := c.rnorm n⁻¹ ((CNz E z).inv_mem hn) (n * x * n⁻¹) hx
      simp only [inv_inv] at h
      rwa [show n⁻¹ * (n * x * n⁻¹) * n = x from by group] at h
  obtain ⟨S, hS_le_CNz⟩ := c.zdata.sylow_CNz
  have hS_le_X : (S : Subgroup G) ≤ X := hS_le_CNz.trans hCNz_le_X
  have hGfac : (Nat.card G).factorization 2 = 21 := by
    let S0 : Sylow 2 G := default
    have h1 : Nat.card ↥(S0 : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
      Sylow.card_eq_multiplicity S0
    have h2 : Nat.card ↥(S0 : Subgroup G) = 2 ^ 21 := c.zdata.syl S0
    have h3 : (2 : ℕ) ^ (Nat.card G).factorization 2 = 2 ^ 21 := by rw [← h1, h2]
    exact Nat.pow_right_injective (a := 2) (by norm_num) h3
  have hX0 : Nat.card ↥X ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hG0 : Nat.card G ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hXfac : (Nat.card ↥X).factorization 2 = 21 := by
    refine le_antisymm ?_ ?_
    · have hdvd : Nat.card ↥X ∣ Nat.card G := Subgroup.card_subgroup_dvd_card X
      have hle : (Nat.card ↥X).factorization 2 ≤ (Nat.card G).factorization 2 :=
        (Nat.factorization_le_iff_dvd hX0 hG0).mpr hdvd 2
      rwa [hGfac] at hle
    · have hd : 2 ^ 21 ∣ Nat.card ↥X := by
        rw [← c.zdata.syl S]
        exact Subgroup.card_dvd_of_le hS_le_X
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX0).mp hd
  have hSsub_fac : (Nat.card ↥((S : Subgroup G).subgroupOf X)).factorization 2 =
      (Nat.card ↥X).factorization 2 := by
    have hScard : Nat.card ↥((S : Subgroup G).subgroupOf X) = 2 ^ 21 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_X).toEquiv]
      exact c.zdata.syl S
    rw [hScard, hXfac]
    exact Nat.factorization_pow_self Nat.prime_two
  have hO2sub : IsPGroup 2 ((TwoFi22.O2In X).subgroupOf X) :=
    (TwoB.isPGroup_O2In X).of_equiv (Subgroup.subgroupOfEquivOfLe (TwoB.O2In_le X)).symm
  have hOn : ((TwoFi22.O2In X).subgroupOf X).Normal := TwoB.normal_subgroupOf_O2In X
  have hOsub_le_Ssub : (TwoFi22.O2In X).subgroupOf X ≤ (S : Subgroup G).subgroupOf X :=
    le_of_normal_two_of_factorization (X := ↥X) hO2sub hOn hSsub_fac
  have hO_le_S : TwoFi22.O2In X ≤ (S : Subgroup G) := by
    intro x hx
    have hxX : x ∈ X := TwoB.O2In_le X hx
    have hxsub : (⟨x, hxX⟩ : ↥X) ∈ (TwoFi22.O2In X).subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    exact hOsub_le_Ssub hxsub
  have hO_le_CNz : TwoFi22.O2In X ≤ CNz E z := hO_le_S.trans hS_le_CNz
  have hO_le_P : TwoFi22.O2In X ≤ Pg E z := by
    refine TwoB.le_O2In hO_le_CNz ?_ (TwoB.isPGroup_O2In X)
    rw [Subgroup.normal_subgroupOf_iff hO_le_CNz]
    intro h k hh hk
    exact (TwoB.normal_subgroupOf_O2In X).conj_mem ⟨h, TwoB.O2In_le X hh⟩ hh
      ⟨k, hCNz_le_X hk⟩
  have hJ_le_X : Jg t z ≤ X := by
    intro j hj
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact c.jr.R_normal j hj x hx
    · intro hx
      have h := c.jr.R_normal j⁻¹ ((Jg t z).inv_mem hj) (j * x * j⁻¹) hx
      simp only [inv_inv] at h
      rwa [show j⁻¹ * (j * x * j⁻¹) * j = x from by group] at h
  have hO_le_R : TwoFi22.O2In X ≤ Rg t z := by
    refine TwoB.le_O2In (hO_le_P.trans c.rp.P_le_J) ?_ (TwoB.isPGroup_O2In X)
    rw [Subgroup.normal_subgroupOf_iff (hO_le_P.trans c.rp.P_le_J)]
    intro h k hh hk
    exact (TwoB.normal_subgroupOf_O2In X).conj_mem ⟨h, TwoB.O2In_le X hh⟩ hh
      ⟨k, hJ_le_X hk⟩
  exact le_antisymm hO_le_R hR_le_O

theorem normalizer_R_le_Cz (c : Core3 E t z) : normalizer (Rg t z : Set G) ≤ Cz z := by
  intro g hg
  rw [mem_Cz]
  have hzR : z ∈ Rg t z := c.jr.V_le_R z_mem_Vtz
  have hgzR : g * z * g⁻¹ ∈ Rg t z := (mem_normalizer_iff.mp hg z).mp hzR
  have hginv : g⁻¹ ∈ normalizer (Rg t z : Set G) := (normalizer (Rg t z : Set G)).inv_mem hg
  have hcent : ∀ y ∈ Rg t z, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) := by
    intro y hy
    have hgy : g⁻¹ * y * g ∈ Rg t z := by
      have h := (mem_normalizer_iff.mp hginv y).mp hy
      simpa using h
    have hcomm : z * (g⁻¹ * y * g) = (g⁻¹ * y * g) * z :=
      (c.jr.center_R z hzR).mpr (Subgroup.mem_zpowers z) (g⁻¹ * y * g) hgy
    calc (g * z * g⁻¹) * y = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by rw [hcomm]
      _ = y * (g * z * g⁻¹) := by group
  have hmem : g * z * g⁻¹ ∈ zpowers z := (c.jr.center_R (g * z * g⁻¹) hgzR).mp hcent
  rcases TwoB.eq_one_or_eq_of_mem_zpowers_two
      (orderOf_eq_prime c.klein.z_sq c.klein.z_ne) hmem with h1 | hz
  · exfalso
    have hz1 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    exact c.klein.z_ne hz1
  · calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hz]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
