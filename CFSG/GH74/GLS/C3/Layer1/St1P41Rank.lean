module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv251C
public import CFSG.GH74.GLS.C3.Layer1.Th2L627N

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpElim

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pPrimeCoreOf_of_cSec {K : Subgroup G} (hKz : Subgroup.center (kBar K) = ⊥) {a : G}
    (haK : a ∈ K) (haS : a ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    a ∈ pPrimeCoreOf 2 K := by
  have hmem : ∀ g : ↥K, (g : G) ∈ pPrimeCoreOf 2 K ↔ g ∈ pPrimeCore 2 ↥K := by
    intro g
    unfold pPrimeCoreOf
    constructor
    · rintro ⟨h, hh, hg⟩
      have : h = g := Subtype.ext hg
      rwa [← this]
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hc : (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : kBar K) ∈ Subgroup.center (kBar K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : ⁅(k : G)⁻¹, a⁆ ∈ pPrimeCoreOf 2 K := haS.2.2 _ (K.inv_mem k.2)
    have h2 : a⁻¹ * ⁅(k : G)⁻¹, a⁆ * a ∈ pPrimeCoreOf 2 K := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem haS.2.1) _).mp h1
      simpa using this
    have h3 : (((k * ⟨a, haK⟩)⁻¹ * (⟨a, haK⟩ * k) : ↥K) : G) = a⁻¹ * ⁅(k : G)⁻¹, a⁆ * a := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact (hmem _).1 (h3 ▸ h2)
  rw [hKz, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact (hmem ⟨a, haK⟩).2 hc

theorem not_mem_pPrimeCoreOf {x : G} {K : Subgroup G} (hx2 : orderOf x = 2)
    (hx : x ∈ pPrimeCoreOf 2 K) : False := by
  have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 K)) := TwoThin.card_pPrimeCoreOf_odd K
  have hord : orderOf x ∣ Nat.card ↥(pPrimeCoreOf 2 K) := Subgroup.orderOf_dvd_natCard _ hx
  have := Odd.of_dvd_nat hodd hord
  rw [hx2] at this
  exact absurd this (by decide)

theorem pRank_add_three_le
    {x : G} {K E : Subgroup G} (hxK : IsIL2Pair x K) (hL : HasL2Model (kBar K) Odd)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hEC : E ≤ CxK x K) (hxE : x ∉ E) :
    pRank 2 ↥E + 3 ≤ pRank 2 G := by
  have hx2 : orderOf x = 2 := hxK.1
  have hxC : x ∈ CxK x K := Iv251.self_mem_CxK hxK.2.1
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    Th2.isElementaryAbelian_zpowers_of_orderOf_two hx2
  have hcd1 : CommDisj E (zpowers x) := by
    refine ⟨fun e he t ht => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
      have : e ∈ centralizer ({x} : Set G) := (hEC he).1
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 this) m).symm.eq.symm
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hx2 hz.2 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.1) hxE
  have hBel := hcd1.isElementaryAbelian_sup' hEel hxel le_rfl le_rfl
  have hBrk : pRank 2 ↥(E ⊔ zpowers x) = pRank 2 ↥E + 1 := by
    rw [hcd1.pRank_sup hEel hxel le_rfl le_rfl, Th2.pRank_zpowers_of_orderOf_two hx2]
  have hBle : E ⊔ zpowers x ≤ CxK x K := sup_le hEC (zpowers_le.2 hxC)
  obtain ⟨m, Q, hm, hQel, hQcard⟩ := Th2.L625.exists_big_of_L2 hxK hL hBel hBle
  have hc1 := C3.Layer1.Back.card_eq_two_pow_pRank hQel
  have hc2 := C3.Layer1.Back.card_eq_two_pow_pRank hBel
  rw [hc2] at hQcard
  rw [hQcard, ← pow_add] at hc1
  have hQrk : pRank 2 ↥Q = pRank 2 ↥(E ⊔ zpowers x) + m :=
    (Nat.pow_right_injective le_rfl hc1).symm
  have h4 := pRank_le_top' Q
  omega

theorem exists_elem_two_of_two_involutions {D : Subgroup G} (hD : IsPGroup 2 ↥D) {u u' : G}
    (hu : u ∈ D) (hu' : u' ∈ D) (hu2 : orderOf u = 2) (hu'2 : orderOf u' = 2) (hne : u ≠ u') :
    ∃ E : Subgroup G, E ≤ D ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ pRank 2 ↥E = 2 := by
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hu
    rw [hu, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  obtain ⟨z₀, hz₀D, hz₀2, hz₀c⟩ := Iv251.exists_central_involution (P := D) (Q := D) hD le_rfl
    Subgroup.le_normalizer hDne
  have key : ∀ w ∈ D, orderOf w = 2 → w ≠ z₀ →
      ∃ E : Subgroup G, E ≤ D ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ pRank 2 ↥E = 2 := by
    intro w hwD hw2 hwz
    have hel0 : CFSG.IsElementaryAbelian 2 ↥(zpowers z₀) :=
      Th2.isElementaryAbelian_zpowers_of_orderOf_two hz₀2
    have hel1 : CFSG.IsElementaryAbelian 2 ↥(zpowers w) :=
      Th2.isElementaryAbelian_zpowers_of_orderOf_two hw2
    have hcd : CommDisj (zpowers z₀) (zpowers w) := by
      refine ⟨fun a ha b hb => ?_, ?_⟩
      · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow (hz₀c w hwD) m n).eq
      · refine eq_bot_iff.2 fun z hz => ?_
        rcases mem_zpowers_two hz₀2 hz.1 with h0 | h0
        · simp [h0]
        · rcases mem_zpowers_two hw2 hz.2 with h1 | h1
          · simp [h1]
          · exact absurd (h1.symm.trans h0) hwz
    refine ⟨zpowers z₀ ⊔ zpowers w, sup_le (zpowers_le.2 hz₀D) (zpowers_le.2 hwD),
      hcd.isElementaryAbelian_sup' hel0 hel1 le_rfl le_rfl, ?_⟩
    rw [hcd.pRank_sup hel0 hel1 le_rfl le_rfl, Th2.pRank_zpowers_of_orderOf_two hz₀2,
      Th2.pRank_zpowers_of_orderOf_two hw2]
  by_cases h : u = z₀
  · exact key u' hu' hu'2 (fun h' => hne (h.trans h'.symm))
  · exact key u hu hu2 h

end CFSG.GH74.GLS.C3.Layer1.PumpElim
