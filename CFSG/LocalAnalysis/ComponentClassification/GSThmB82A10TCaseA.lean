module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCases

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

private abbrev fixR : Finset (Fin 10) := {0, 1, 2, 3, 4, 5, 6, 7}

private theorem mem_fixR_of_r0 : ∀ i : Fin 10, r0 i = i → i ∈ fixR := by
  decide

private theorem r0_of_mem_fixR : ∀ i : Fin 10, i ∈ fixR → r0 i = i := by
  decide

namespace Ctx.PropBData

variable {c : Ctx X} (d : c.PropBData)

theorem conjugate_J : conjugate c.s.h.J d.g ≤ centralizer ({d.a'} : Set X) ∧
    IsPComponent 2 ((conjugate c.s.h.J d.g).subgroupOf (centralizer ({d.a'} : Set X))) ∧
    Nat.card (↥(conjugate c.s.h.J d.g) ⧸ pPrimeCore 2 ↥(conjugate c.s.h.J d.g)) = 360 ∧
    d.z' ∈ conjugate c.s.h.J d.g := by
  obtain ⟨h1, h2⟩ := Six.isPComponent_conjugate c.s.h.J_le c.s.h.isPComponent_J d.g
  rw [conjugate_centralizer_singleton] at h1 h2
  refine ⟨h1, h2, ?_, conj_mem_conjugate (mem_inf.mp c.Z.hzD).2 d.g⟩
  let e : ↥c.s.h.J ≃* ↥(conjugate c.s.h.J d.g) :=
    c.s.h.J.equivMapOfInjective (MulAut.conj d.g⁻¹).toMonoidHom (MulAut.conj d.g⁻¹).injective
  rw [← c.card_J]
  exact (Nat.card_congr (QuotientGroup.congr (pPrimeCore 2 ↥c.s.h.J)
    (pPrimeCore 2 ↥(conjugate c.s.h.J d.g)) e (pPrimeCore_map_iso 2 e)).toEquiv).symm

theorem B0_le_centralizer_a' : c.s.h.secB0 c.s.y ≤ centralizer ({d.a'} : Set X) := fun b hb =>
  mem_centralizer_singleton_iff.mpr (d.comm_S0 _ (Set.mem_insert _ _) b
    (mem_inf.mpr ⟨c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hb), le_normalizer hb⟩))

private theorem inf_oddCoreIn_le_oddCoreIn {H Y : Subgroup X} (hYH : Y ≤ H) :
    Y ⊓ oddCoreIn H ≤ oddCoreIn Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : ((Y ⊓ oddCoreIn H).subgroupOf Y).Normal := by
    rw [normal_subgroupOf_iff inf_le_left]
    intro k y hk hy
    obtain ⟨hkY, hkO⟩ := mem_inf.mp hk
    refine mem_inf.mpr ⟨mul_mem (mul_mem hy hkY) (inv_mem hy), ?_⟩
    obtain ⟨o, ho, rfl⟩ := mem_map.mp hkO
    exact ⟨⟨y, hYH hy⟩ * o * ⟨y, hYH hy⟩⁻¹,
      (inferInstance : (pPrimeCore 2 ↥H).Normal).conj_mem o ho _, rfl⟩
  have hKc : Nat.Coprime 2 (Nat.card ((Y ⊓ oddCoreIn H).subgroupOf Y)) := by
    have h1 : Nat.card ((Y ⊓ oddCoreIn H).subgroupOf Y) ∣ Nat.card (pPrimeCore 2 ↥H) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,
        Nat.card_congr ((pPrimeCore 2 ↥H).equivMapOfInjective H.subtype
          H.subtype_injective).toEquiv]
      exact card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hK : (Y ⊓ oddCoreIn H).subgroupOf Y ≤ pPrimeCore 2 ↥Y := le_sSup ⟨hKn, hKc⟩
  intro x hx
  exact ⟨⟨x, (mem_inf.mp hx).1⟩, hK (mem_subgroupOf.mpr hx), rfl⟩

theorem mem_coreActionKernel_of_card_lt {Y : Subgroup X}
    (hYC : Y ≤ centralizer ({d.a'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X))
    (hY : IsPComponent 2 (Y.subgroupOf
      (centralizer ({d.a'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X))))
    (hcard : 360 < Nat.card (↥Y ⧸ Open.fusionZStar ↥Y))
    (hzY : d.z' ∈ normalizer (Y : Set X)) : d.z' ∈ coreActionKernel Y := by
  obtain ⟨hJC, hJpc, hJcard, hzJ⟩ := d.conjugate_J
  have hYlay : Y ≤ layerIn (centralizer ({d.a'} : Set X)) :=
    le_layerIn_of_isPComponent_inf_centralizer (c.s.h.isPGroup_secB0 c.s.y)
      (d.B0_le_centralizer_a'.trans le_normalizer) hYC hY
  have hle := card_quot_fusionZStar_le ↥(conjugate c.s.h.J d.g)
  have hlt : Nat.card (↥(conjugate c.s.h.J d.g) ⧸ Open.fusionZStar ↥(conjugate c.s.h.J d.g)) <
      Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) := by omega
  have hcomm := commutator_le_oddCoreIn_of_card_lt hJC hJpc hYlay
    (isPerfect_of_isPComponent hYC hY) (isQuasisimple_of_isPComponent hYC hY) hlt
  refine mem_coreActionKernel.mpr ⟨hzY, fun y hy => ?_⟩
  have h1 : y⁻¹ * d.z'⁻¹ * y * d.z' ∈ ⁅Y, conjugate c.s.h.J d.g⁆ := by
    have h2 := commutator_mem_commutator (inv_mem hy) (inv_mem hzJ)
    rwa [commutatorElement_def, inv_inv, inv_inv] at h2
  have h2 : y⁻¹ * d.z'⁻¹ * y * d.z' ∈ Y := by
    have h3 : d.z'⁻¹ * y * d.z'⁻¹⁻¹ ∈ Y := (mem_normalizer_iff.mp (inv_mem hzY) y).mp hy
    rw [inv_inv] at h3
    rw [show y⁻¹ * d.z'⁻¹ * y * d.z' = y⁻¹ * (d.z'⁻¹ * y * d.z') by group]
    exact mul_mem (inv_mem hy) h3
  exact inf_oddCoreIn_le_oddCoreIn (hYC.trans inf_le_left) (mem_inf.mpr ⟨h2, hcomm h1⟩)

theorem false_of_case_i (ha : d.a' ∈ c.s.h.secB0 c.s.y)
    (hz : c.φ ⟨d.z', d.z'_mem_secSub⟩ = sigmaTwo * z0) : False := by
  have hLB : Seven.Lay c.s.h c.s.y ≤ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    Seven.Lay_le_centralizer_secB0 _ _
  have hBa : centralizer (c.s.h.secB0 c.s.y : Set X) ≤ centralizer ({d.a'} : Set X) :=
    centralizer_le (Set.singleton_subset_iff.mpr ha)
  have hCeq : centralizer ({d.a'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) =
      centralizer (c.s.h.secB0 c.s.y : Set X) := inf_of_le_right hBa
  have hzL : d.z' ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) :=
    Seven.secG0_le_normalizer_Lay _ _ (mem_inf.mp d.z'_mem_S0).2
  have hcard : 360 < Nat.card (↥(Seven.Lay c.s.h c.s.y) ⧸
      Open.fusionZStar ↥(Seven.Lay c.s.h c.s.y)) := by
    obtain ⟨e⟩ := c.nonempty_Lay_equiv
    rw [EvenPump.fusionZStar_eq_of_alt (by norm_num) e, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hk := d.mem_coreActionKernel_of_card_lt (le_inf (hLB.trans hBa) hLB)
    (by rw [hCeq]; exact c.s.L_pc) hcard hzL
  have h1 := (c.isRep_Lay.mem_coreActionKernel_iff_eq_one (by norm_num) d.z'_mem_secSub hzL).mp hk
  rw [hz] at h1
  exact absurd h1 (by decide)

theorem false_of_case_iii (ha : c.φ ⟨d.a', d.a'_mem_secSub⟩ = r0)
    (hz : c.φ ⟨d.z', d.z'_mem_secSub⟩ = sigmaTwo * z0 * r0) : False := by
  have hLB : Seven.Lay c.s.h c.s.y ≤ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    Seven.Lay_le_centralizer_secB0 _ _
  have hG0L : c.s.h.secG0 c.s.y ≤ normalizer (Seven.Lay c.s.h c.s.y : Set X) :=
    Seven.secG0_le_normalizer_Lay _ _
  have haL : d.a' ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) := hG0L (mem_inf.mp d.a'_mem_S0).2
  have hzL : d.z' ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) := hG0L (mem_inf.mp d.z'_mem_S0).2
  have hEN : zpowers d.a' ≤ c.s.h.secSub c.s.y := zpowers_le.mpr d.a'_mem_secSub
  have hE2 : IsPGroup 2 (zpowers d.a') := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact d.a'_mul_self))
  have hφpow : ∀ k : ℤ, c.φ ⟨d.a' ^ k, hEN (zpow_mem (mem_zpowers _) k)⟩ = r0 ^ k := by
    intro k
    rw [← ha, ← map_zpow]
    rfl
  have hΔ : ∀ i, (∀ e (he : e ∈ zpowers d.a'), c.φ ⟨e, hEN he⟩ i = i) ↔ i ∈ fixR := by
    intro i
    constructor
    · intro h
      have h1 := h d.a' (mem_zpowers _)
      rw [ha] at h1
      exact mem_fixR_of_r0 i h1
    · intro hi e he
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
      rw [hφpow k]
      exact zpow_apply_eq_self_of_apply_eq_self (r0_of_mem_fixR i hi) k
  obtain ⟨Y, hYC, hYpc, hYrep, -, -, hYN⟩ :=
    exists_natural_component c.isRep_Lay hEN (zpowers_le.mpr haL) hE2 hΔ (by decide)
  rw [UnbalancedLayer.centralizer_zpowers_eq] at hYC hYpc
  have hUV : Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.a'} : Set X) ≤
      centralizer ({d.a'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    le_inf inf_le_right (inf_le_left.trans hLB)
  have hUn : ((Seven.Lay c.s.h c.s.y ⊓ centralizer ({d.a'} : Set X)).subgroupOf
      (centralizer ({d.a'} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X))).Normal := by
    rw [normal_subgroupOf_iff hUV]
    intro h k hh hk
    obtain ⟨hhL, hha⟩ := mem_inf.mp hh
    obtain ⟨hka, hkB⟩ := mem_inf.mp hk
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hG0L (centralizer_le_normalizer _ hkB)) h).mp hhL,
      mul_mem (mul_mem hka hha) (inv_mem hka)⟩
  have hY := isPComponent_of_le_of_subnormal hYC hUV hUn.isSubnormal hYpc
  have hcard : 360 < Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) := by
    obtain ⟨e⟩ := hYrep.nonempty_equiv
    have h8 : 4 ≤ Nat.card ↥fixR := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      decide
    have hZ : center (↥Y ⧸ pPrimeCore 2 ↥Y) = ⊥ := by
      let e' := e.trans (altOnEquiv fixR).symm
      have h1 := Subgroup.map_center_eq e'
      rw [alternatingGroup.center_eq_bot h8] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1
    rw [fusionZStar_eq_of_center_eq_bot hZ, Nat.card_congr e.toEquiv, card_altOn _ (by decide)]
    decide
  have hzE : d.z' ∈ normalizer ((zpowers d.a' : Subgroup X) : Set X) := by
    refine centralizer_le_normalizer _ ?_
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact mem_centralizer_singleton_iff.mpr d.a'_comm_z'.symm
  have hzY : d.z' ∈ normalizer (Y : Set X) :=
    hYN (mem_inf.mpr ⟨mem_inf.mpr ⟨d.z'_mem_secSub, hzL⟩, hzE⟩)
  have hk := d.mem_coreActionKernel_of_card_lt (le_inf (hYC.trans inf_le_right)
    (hYC.trans (inf_le_left.trans hLB))) hY hcard hzY
  have h1 := hYrep.fix_of_mem_coreActionKernel (by decide) d.z'_mem_secSub hzY hk 0 (by decide)
  rw [hz] at h1
  exact absurd h1 (by decide)

end Ctx.PropBData

end CFSG.ComponentClassification.GSThmB.A10T
