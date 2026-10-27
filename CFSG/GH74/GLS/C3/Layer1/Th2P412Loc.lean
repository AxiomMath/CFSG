module

public import CFSG.GroupTheory.PrimeCorefreeQuasisimple

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG
open scoped commutatorElement

section Zsyl

variable {D : Type} [Group D] [Finite D]

theorem le_sup_pPrimeCore_of_central_sylow {V Ω : Subgroup D} [Ω.Normal] (hVc : V ≤ center D)
    (hV2 : IsPGroup 2 ↥V) (hVΩ : V ≤ Ω) (hodd : Odd (V.relIndex Ω)) :
    Ω ≤ V ⊔ pPrimeCore 2 D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVΩc : V.subgroupOf Ω ≤ center Ω := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro b
    have hc := Subgroup.mem_center_iff.1 (hVc (Subgroup.mem_subgroupOf.1 ha)) (b : D)
    exact Subtype.ext hc
  have hVΩn : (V.subgroupOf Ω).Normal := CFSG.GroupTheory.normal_of_le_center hVΩc
  have hcard : Nat.card (V.subgroupOf Ω) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVΩ).toEquiv
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (V.subgroupOf Ω)) (V.subgroupOf Ω).index := by
    rw [hcard, hn]
    exact (Nat.coprime_two_left.2 hodd).pow_left n
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Odd (Nat.card H) := by
    have h1 : (V.subgroupOf Ω).index = Nat.card H := hH.symm.index_eq_card
    rw [← h1]
    exact hodd
  have hHord : ∀ h : Ω, h ∈ H → Odd (orderOf h) := fun h hh =>
    Odd.of_dvd_nat hHcard (Subgroup.orderOf_dvd_natCard H hh)
  have hOddH : ∀ w : Ω, Odd (orderOf w) → w ∈ H := by
    intro w hw
    obtain ⟨⟨⟨a, ha⟩, ⟨h, hh⟩⟩, hwa⟩ := hH.2 w
    have hwa' : a * h = w := hwa
    have hac : a ∈ center Ω := hVΩc ha
    have hah : a * h = h * a := (Subgroup.mem_center_iff.1 hac h).symm
    have hcomm : Commute w h⁻¹ := by
      show w * h⁻¹ = h⁻¹ * w
      rw [← hwa']
      calc a * h * h⁻¹ = a := by group
        _ = h⁻¹ * (a * h) := by rw [hah]; group
    have ha_eq : a = w * h⁻¹ := by rw [← hwa']; group
    have hord1 : orderOf a ∣ Nat.lcm (orderOf w) (orderOf h⁻¹) := by
      rw [ha_eq]
      exact hcomm.orderOf_mul_dvd_lcm
    have hlcm : Odd (Nat.lcm (orderOf w) (orderOf h⁻¹)) := by
      have hhinv : Odd (orderOf h⁻¹) := by
        rw [orderOf_inv]
        exact hHord h hh
      exact Odd.of_dvd_nat (hw.mul hhinv) (Nat.lcm_dvd_mul _ _)
    have hao : Odd (orderOf a) := Odd.of_dvd_nat hlcm hord1
    have haV : (a : D) ∈ V := Subgroup.mem_subgroupOf.1 ha
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hV2) ⟨(a : D), haV⟩
    have hk' : orderOf (a : D) = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
    have hk0 : k = 0 := by
      by_contra hk0
      have h1 : orderOf a = 2 ^ k := by rwa [Subgroup.orderOf_coe] at hk'
      exact (Nat.not_even_iff_odd.2 hao) (h1 ▸ Nat.even_pow.2 ⟨even_two, hk0⟩)
    have ha1 : a = 1 := by
      have h1 : orderOf a = 1 := by
        rw [← Subgroup.orderOf_coe, hk', hk0, pow_zero]
      exact orderOf_eq_one_iff.1 h1
    rw [← hwa', ha1, one_mul]
    exact hh
  set H' : Subgroup D := H.map Ω.subtype with hH'
  have hH'card : Odd (Nat.card H') := by
    rw [hH', Subgroup.card_map_of_injective Ω.subtype_injective]
    exact hHcard
  have hH'n : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hn
    have hmem : g * (h : D) * g⁻¹ ∈ Ω := ‹Ω.Normal›.conj_mem _ h.2 g
    refine ⟨⟨g * (h : D) * g⁻¹, hmem⟩, ?_, rfl⟩
    apply hOddH
    have hord : orderOf (g * (h : D) * g⁻¹) = orderOf (h : D) := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (h : D)
      simpa [MulAut.conj_apply] using this
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mk, hord, Subgroup.orderOf_coe]
    exact hHord h hh
  have hH'le : H' ≤ pPrimeCore 2 D :=
    CFSG.GroupTheory.le_pPrimeCore_of_normal hH'n (Nat.coprime_two_left.2 hH'card)
  intro ω hω
  obtain ⟨⟨⟨a, ha⟩, ⟨h, hh⟩⟩, hwa⟩ := hH.2 ⟨ω, hω⟩
  have hωeq : (a : D) * (h : D) = ω := congrArg Subtype.val hwa
  rw [← hωeq]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 ha) (hH'le ⟨h, hh, rfl⟩)

end Zsyl

end CFSG.GH74.GLS.Th2.P412
