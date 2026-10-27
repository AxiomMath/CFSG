module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open
open scoped Pointwise

section ZStarStep

variable {G : Type} [Group G] [Finite G]

theorem odd_card_oddCore (H : Type) [Group H] [Finite H] : Odd (Nat.card (CFSG.oddCore H)) := by
  have hle : CFSG.oddCore H ≤ CFSG.pPrimeCore 2 H :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hle) (CFSG.pPrimeCore_coprime_card (p := 2) (G := H)))

theorem eq_one_or_of_mem_zpowers_of_mul_self {H : Type} [Group H] {a x : H} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem odd_elt_eq_one_of_central (hO : classicalInvolutionOddCore G = ⊥) (R N : Subgroup G) [R.Normal]
    [N.Normal] (hN2 : IsPGroup 2 N) (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n = n * r)
    (hodd : Odd (N.subgroupOf R).index) {y : G} (hyR : y ∈ R) (hy : Odd (orderOf y)) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup ↥R := N.subgroupOf R with hZ
  have hZn : Z.Normal := Subgroup.normal_subgroupOf
  have hZ2 : IsPGroup 2 Z := hN2.comap_subtype
  have hZc : ∀ r : ↥R, ∀ z ∈ Z, z * r = r * z := fun r z hz =>
    Subtype.ext (hRN (r : G) r.2 (z : G) (Subgroup.mem_subgroupOf.mp hz)).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hZ2)
  have hcop : (Nat.card Z).Coprime Z.index := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHodd : Odd (Nat.card H) := by rw [← hH.symm.index_eq_card]; exact hodd
  have hOddH : ∀ g : ↥R, Odd (orderOf g) → g ∈ H := by
    intro g hg
    have hmem : g ∈ Z ⊔ H := by rw [hH.sup_eq_top]; exact Subgroup.mem_top g
    have hmem' : g ∈ ((Z ⊔ H : Subgroup ↥R) : Set ↥R) := hmem
    rw [Subgroup.normal_mul] at hmem'
    obtain ⟨z, hz, h, hh, rfl⟩ := hmem'
    have hcomm : Commute z h := hZc h z hz
    have hpow : (z * h) ^ orderOf (z * h) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at hpow
    have h1 : z ^ orderOf (z * h) = (h ^ orderOf (z * h))⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have h2 : z ^ orderOf (z * h) ∈ Z ⊓ H :=
      ⟨Z.pow_mem hz _, by rw [h1]; exact H.inv_mem (H.pow_mem hh _)⟩
    have h3 : z ^ orderOf (z * h) = 1 := Subgroup.disjoint_def.mp hH.disjoint h2.1 h2.2
    have hz2 : orderOf z ∣ orderOf (z * h) := orderOf_dvd_of_pow_eq_one h3
    have hzodd : Odd (orderOf z) := Odd.of_dvd_nat hg hz2
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hZ2) ⟨z, hz⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj0 : j = 0 := by
      by_contra hne
      have : Even (orderOf z) := by rw [hj]; exact (Nat.even_pow.mpr ⟨even_two, hne⟩)
      exact (Nat.not_even_iff_odd.mpr hzodd) this
    have hz1 : z = 1 := by rw [hj0, pow_zero] at hj; exact orderOf_eq_one_iff.mp hj
    have hzh : z * h = h := by rw [hz1, one_mul]
    show z * h ∈ H
    rw [hzh]
    exact hh
  have hHord : ∀ h ∈ H, Odd (orderOf h) := fun h hh => by
    have := orderOf_dvd_natCard (⟨h, hh⟩ : H)
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hHodd this
  set H' : Subgroup G := H.map R.subtype with hH'
  have hHn : H'.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨h, hh, rfl⟩ := ha
    have hgR : g * (h : G) * g⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem _ h.2 g
    have hord : orderOf (⟨g * (h : G) * g⁻¹, hgR⟩ : ↥R) = orderOf h := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe h]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
    have : (⟨g * (h : G) * g⁻¹, hgR⟩ : ↥R) ∈ H :=
      hOddH _ (by rw [hord]; exact hHord h hh)
    exact ⟨_, this, rfl⟩
  have hH'odd : Odd (Nat.card H') := by
    have e := Nat.card_congr (Subgroup.equivMapOfInjective H R.subtype R.subtype_injective).toEquiv
    rw [hH', ← e]
    exact hHodd
  have hle : H' ≤ classicalInvolutionOddCore G := le_sSup ⟨hHn, hH'odd⟩
  rw [hO] at hle
  have hyH : (⟨y, hyR⟩ : ↥R) ∈ H := hOddH _ (by rw [Subgroup.orderOf_mk]; exact hy)
  have : y ∈ H' := ⟨_, hyH, rfl⟩
  exact (Subgroup.mem_bot.mp (hle this))

end ZStarStep

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
