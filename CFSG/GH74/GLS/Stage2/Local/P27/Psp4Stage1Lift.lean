module

public import CFSG.GH74.GLS.Stage2.Local.Bar

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G] [Finite G] {z : G}

theorem lift_odd_orderOf_of_toBar_eq_one (w : ↥(Cen z)) (hw : toBar z w = 1) :
    Odd (orderOf w) := by
  have h1 : w ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar]; exact hw
  have hd : orderOf (⟨w, h1⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣ Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hd
  exact Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))) hd

theorem mem_of_toBar_mem {I Y : Subgroup G} (hIY : I ≤ Y) (hYC : Y ≤ Cen z)
    (hn : (I.subgroupOf Y).Normal) {u : G} (huY : u ∈ Y) (hu2 : ∃ k : ℕ, u ^ 2 ^ k = 1)
    (hu : toBar z ⟨u, hYC huY⟩ ∈ barOf z I) : u ∈ I := by
  obtain ⟨k, hk⟩ := hu2
  obtain ⟨c, hc, hcu⟩ := hu
  have hcI : (c : G) ∈ I := Subgroup.mem_subgroupOf.1 hc
  have hcY : (c : G) ∈ Y := hIY hcI
  have hw : toBar z (c⁻¹ * ⟨u, hYC huY⟩) = 1 := by
    rw [map_mul, map_inv, hcu, inv_mul_cancel]
  have hodd := lift_odd_orderOf_of_toBar_eq_one _ hw
  have := hn
  let π : ↥Y →* ↥Y ⧸ I.subgroupOf Y := QuotientGroup.mk' (I.subgroupOf Y)
  let cY : ↥Y := ⟨c, hcY⟩
  let uY : ↥Y := ⟨u, huY⟩
  have hπc : π cY = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hcI)
  have hπu : π uY = π (cY⁻¹ * uY) := by
    rw [map_mul, map_inv, hπc, inv_one, one_mul]
  have hord_w : orderOf (cY⁻¹ * uY) = orderOf (c⁻¹ * ⟨u, hYC huY⟩ : ↥(Cen z)) :=
    (Subgroup.orderOf_coe (cY⁻¹ * uY)).symm.trans
      (Subgroup.orderOf_coe (c⁻¹ * ⟨u, hYC huY⟩ : ↥(Cen z)))
  have huk : uY ^ 2 ^ k = 1 := Subtype.ext hk
  have h1 : orderOf (π uY) ∣ 2 ^ k := (orderOf_map_dvd π uY).trans (orderOf_dvd_of_pow_eq_one huk)
  have h2 : orderOf (π uY) ∣ orderOf (c⁻¹ * ⟨u, hYC huY⟩ : ↥(Cen z)) := by
    rw [hπu]
    exact (orderOf_map_dvd π _).trans (dvd_of_eq hord_w)
  have h3 : orderOf (π uY) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)) h1 h2
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3))

theorem factorization_card_barOf {X : Subgroup G} (hX : X ≤ Cen z) :
    (Nat.card ↥X).factorization 2 = (Nat.card ↥(barOf z X)).factorization 2 := by
  let f : ↥X →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hX)
  have hrange : f.range = barOf z X := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨Subgroup.inclusion hX s, Subgroup.mem_subgroupOf.2 s.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, Subgroup.mem_subgroupOf.1 hc⟩, rfl⟩
  have hker : Odd (Nat.card f.ker) := by
    have hle : f.ker.map (Subgroup.inclusion hX) ≤ (toBar z).ker := by
      rintro _ ⟨s, hs, rfl⟩
      exact hs
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hX)]
    exact Odd.of_dvd_nat (odd_card_ker_toBar z) (Subgroup.card_dvd_of_le hle)
  have hcard : Nat.card f.ker * Nat.card ↥(barOf z X) = Nat.card ↥X := by
    rw [← hrange]; exact Subgroup.card_ker_mul_card_range f
  have hX0 : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
  have hk0 : Nat.card f.ker ≠ 0 := left_ne_zero_of_mul (hcard ▸ hX0)
  have hb0 : Nat.card ↥(barOf z X) ≠ 0 := right_ne_zero_of_mul (hcard ▸ hX0)
  have hdiv : ¬ 2 ∣ Nat.card f.ker := fun h => (Nat.not_even_iff_odd.2 hker) (even_iff_two_dvd.2 h)
  rw [← hcard, Nat.factorization_mul hk0 hb0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hdiv, zero_add]

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1
