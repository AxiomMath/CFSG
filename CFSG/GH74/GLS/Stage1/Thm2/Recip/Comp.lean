module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cSec_conj (K : Subgroup G) {n c : G} (hn : n ∈ normalizer (K : Set G)) (hc : c ∈ cSec K) :
    n * c * n⁻¹ ∈ cSec K := by
  obtain ⟨hcK, hcM, hcc⟩ := hc
  have hnM : n ∈ normalizer (pPrimeCoreOf 2 K : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf hn
  refine ⟨mul_mem (mul_mem hn hcK) (inv_mem hn), mul_mem (mul_mem hnM hcM) (inv_mem hnM),
    fun k hk => ?_⟩
  have hk' : n⁻¹ * k * n ∈ K := by simpa using (mem_normalizer_iff.mp (inv_mem hn) k).mp hk
  have h := hcc (n⁻¹ * k * n) hk'
  have e : ⁅k, n * c * n⁻¹⁆ = n * ⁅n⁻¹ * k * n, c⁆ * n⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (mem_normalizer_iff.mp hnM _).mp h

omit [Finite G] in
def innSub (K : Subgroup G) : Subgroup G where
  carrier := {g | ∃ k ∈ K, g * k⁻¹ ∈ cSec K}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
    refine ⟨k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
    have e : a * b * (k₁ * k₂)⁻¹ = (a * k₁⁻¹) * (k₁ * (b * k₂⁻¹) * k₁⁻¹) := by group
    rw [e]
    exact mul_mem h₁ (cSec_conj K (le_normalizer hk₁) h₂)
  inv_mem' := by
    rintro a ⟨k, hk, h⟩
    refine ⟨k⁻¹, inv_mem hk, ?_⟩
    have e : a⁻¹ * (k⁻¹)⁻¹ = k⁻¹ * (a * k⁻¹)⁻¹ * k⁻¹⁻¹ := by group
    rw [e]
    exact cSec_conj K (le_normalizer (inv_mem hk)) (inv_mem h)

omit [Finite G] in
theorem mem_innSub_iff {K : Subgroup G} {s : G} : s ∈ innSub K ↔ InducesInner s K := Iff.rfl

omit [Finite G] in
theorem le_innSub (K : Subgroup G) : K ≤ innSub K := fun k hk => ⟨k, hk, by simp⟩

omit [Finite G] in
theorem cSec_le_innSub (K : Subgroup G) : cSec K ≤ innSub K := fun c hc =>
  ⟨1, one_mem _, by simpa using hc⟩

omit [Finite G] in
theorem innSub_le_normalizer (K : Subgroup G) : innSub K ≤ normalizer (K : Set G) := by
  rintro g ⟨k, hk, h⟩
  have : g = (g * k⁻¹) * k := by group
  rw [this]
  exact mul_mem h.1 (le_normalizer hk)

theorem le_cSec_of_ne {X K₁ K₂ : Subgroup G} (h₁ : IsPCompIn 2 X K₁) (h₂ : IsPCompIn 2 X K₂)
    (hne : K₁ ≠ K₂) : K₁ ≤ cSec K₂ := by
  obtain ⟨hK₁X, hK₁2⟩ := TwoThin.isPCompIn_two_iff.mp h₁
  obtain ⟨hK₂X, hK₂2⟩ := TwoThin.isPCompIn_two_iff.mp h₂
  have c1 := TwoThin.isComponent_map_barMk hK₁2
  have c2 := TwoThin.isComponent_map_barMk hK₂2
  have hne' : (K₁.subgroupOf X).map (TwoThin.barMk ↥X) ≠
      (K₂.subgroupOf X).map (TwoThin.barMk ↥X) := by
    intro h
    apply hne
    have h3 := OddKernelTwoComponents.lift_unique (TwoThin.barMk ↥X) TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk _ _ hK₁2 hK₂2 h
    have h4 := Subgroup.subgroupOf_inj.mp h3
    rwa [inf_eq_left.mpr hK₁X, inf_eq_left.mpr hK₂X] at h4
  have hcomm := (CFSG.LocalCores.distinct_components_commute c1 c2).resolve_left hne'
  intro q hq
  have hqX : q ∈ X := hK₁X hq
  refine TwoThin.mem_centralizerSection_of_map_eq hK₂X hK₂2 hqX ?_
  intro m hm
  have hq' : (⟨q, hqX⟩ : ↥X) ∈ K₁.subgroupOf X := hq
  have h1 : TwoThin.barMk ↥X ⟨q, hqX⟩ ∈ (K₁.subgroupOf X).map (TwoThin.barMk ↥X) :=
    Subgroup.mem_map_of_mem _ hq'
  have h2 : TwoThin.barMk ↥X m ∈ (K₂.subgroupOf X).map (TwoThin.barMk ↥X) :=
    Subgroup.mem_map_of_mem _ hm
  have h3 := Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  rw [map_mul, map_mul, map_inv, h3, mul_inv_cancel_right]

theorem pLayerOf_le_innSub {X K : Subgroup G} (hK : IsPCompIn 2 X K) :
    pLayerOf 2 X ≤ innSub K := by
  refine sSup_le fun L hL => ?_
  by_cases h : L = K
  · rw [h]
    exact le_innSub K
  · exact (le_cSec_of_ne hL hK h).trans (cSec_le_innSub K)

theorem pLayerOf_le_normalizer {X K : Subgroup G} (hK : IsPCompIn 2 X K) :
    pLayerOf 2 X ≤ normalizer (K : Set G) :=
  (pLayerOf_le_innSub hK).trans (innSub_le_normalizer K)

theorem O22_le_cSec {X K : Subgroup G} (hK : IsPCompIn 2 X K) : O22 X ≤ cSec K := by
  obtain ⟨hKX, hK2⟩ := TwoThin.isPCompIn_two_iff.mp hK
  rintro _ ⟨g, hg, rfl⟩
  refine TwoThin.mem_centralizerSection_of_map_eq hKX hK2 g.2 ?_
  intro m hm
  have hgπ : TwoThin.barMk ↥X g ∈ pCore 2 (TwoThin.barQ ↥X) := hg
  have c1 := TwoThin.isComponent_map_barMk hK2
  have hp : IsPGroup 2 ↥(pCore 2 (TwoThin.barQ ↥X)) := pCore_isPGroup
  have : Group.IsNilpotent ↥(pCore 2 (TwoThin.barQ ↥X)) := hp.isNilpotent
  have hR : Group.IsSolvable ↥(pCore 2 (TwoThin.barQ ↥X)) := inferInstance
  have : (pCore 2 (TwoThin.barQ ↥X)).Normal := pCore_normal
  have hsub : (pCore 2 (TwoThin.barQ ↥X)).IsSubnormal :=
    Subgroup.IsSubnormal.step _ ⊤ le_top Subgroup.IsSubnormal.top inferInstance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hR hsub).1 _ c1
  have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem (TwoThin.barMk ↥X) hm) hgπ
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  show TwoThin.barMk ↥X (g * m * g⁻¹) = TwoThin.barMk ↥X m
  rw [map_mul, map_mul, map_inv, ← h1]
  simp

theorem le_pLayerOf_of_isPCompIn_inf {s t : G} (hs : orderOf s = 2)
    (hst : s ∈ centralizer ({t} : Set G)) {Λ : Subgroup G}
    (hΛ : IsPCompIn 2 (centralizer ({s} : Set G) ⊓ centralizer ({t} : Set G)) Λ) :
    Λ ≤ pLayerOf 2 (centralizer ({t} : Set G)) := by
  have hso : orderOf (⟨s, hst⟩ : ↥(centralizer ({t} : Set G))) = 2 :=
    TwoThin.orderOf_mk_centralizer hst hs
  have hΛC := TwoThin.le_centralizer_mk (TwoThin.isPCompIn_two_iff.mp hΛ).1 hst
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hΛ hst
  obtain ⟨hΛE, -⟩ := TwoThin.pumpupY_structure hso hΛC hΛ2
  rw [TwoThin.pLayerOf_two_eq_map]
  intro g hg
  have hgC : g ∈ centralizer ({t} : Set G) := (hΛ.1 hg).2
  exact ⟨⟨g, hgC⟩, hΛE (Subgroup.mem_subgroupOf.mpr hg), rfl⟩

theorem isPComponent_top {F : Type*} [Group F] [Finite F] (hq : IsQuasisimple F)
    (hc : pPrimeCore 2 F = ⊥) : IsPComponent 2 (⊤ : Subgroup F) := by
  have hker : (QuotientGroup.mk' (pPrimeCore 2 F)).ker = ⊥ := by rw [QuotientGroup.ker_mk', hc]
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 F)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsurj := QuotientGroup.mk'_surjective (pPrimeCore 2 F)
  refine ⟨⊤, ⟨?_, Subgroup.IsSubnormal.top⟩, Subgroup.IsSubnormal.top,
    Subgroup.map_top_of_surjective _ hsurj, ?_⟩
  · let e : F ≃* (F ⧸ pPrimeCore 2 F) := MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj, hsurj⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.trans Subgroup.topEquiv.symm) hq
  · intro J hJ _ hmapJ
    have := Subgroup.map_injective hinj
      (hmapJ.trans (Subgroup.map_top_of_surjective _ hsurj).symm)
    exact hJ.ne this

omit [Finite G] in
theorem centralizer_ne_top {t : G} (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (ht : orderOf t = 2) : centralizer ({t} : Set G) ≠ ⊤ := by
  intro h
  have hz : t ∈ center G := by
    rw [mem_center_iff]
    intro g
    have : g ∈ centralizer ({t} : Set G) := by rw [h]; exact mem_top g
    exact ((mem_centralizer_iff.mp this) t (Set.mem_singleton t)).symm
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h1 | h1
  · rw [h1, mem_bot] at hz
    exact ne_one_of_orderOf_eq_two ht hz
  · obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : a ∈ center G := by rw [h1]; exact mem_top a
    exact (mem_center_iff.mp this b).symm

theorem isKGroupNative_hat (hG : IsKProperSimple G) {t : G} (ht : orderOf t = 2) {K : Subgroup G}
    (hK : K ≤ centralizer ({t} : Set G)) : IsKGroupNative (Hat K) := by
  have hC : IsKGroupNative ↥(centralizer ({t} : Set G)) :=
    hG.isKGroupNative_of_ne_top (centralizer_ne_top hG.1 hG.2.1 ht)
  have h1 : SectionRank.IsKGroupCat ↥(K.subgroupOf (centralizer ({t} : Set G))) :=
    SectionRank.IsKGroupCat.subgroup hC _
  have h2 : SectionRank.IsKGroupCat ↥K :=
    SectionRank.IsKGroupCat.of_mulEquiv h1 (Subgroup.subgroupOfEquivOfLe hK).symm
  exact SectionRank.IsKGroupCat.quotient h2 (pPrimeCore 2 ↥K)

theorem pRank_hat (K : Subgroup G) : pRank 2 (Hat K) = pRank 2 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) := by
    have := TwoThin.odd_card_pPrimeCore ↥K
    exact fun h => (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact SectionRank.pRank_quotient_eq (pPrimeCore 2 ↥K) hN

theorem inducesFAut_of_mem_cSec (hG : IsKProperSimple G) {t : G} (ht : orderOf t = 2)
    {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({t} : Set G)) K) (hr : pRank 2 ↥K = 1)
    {s : G} (hs : s ∈ cSec K) : InducesFAut s K := by
  refine ⟨hs.1, ?_⟩
  have h1 : inducedQuotAut K (pPrimeCore 2 ↥K) ⟨s, hs.1⟩ = 1 := (phi_eq_one_iff K hs.1).mpr hs
  rw [h1]
  refine ⟨TwoThin.isQuasisimple_hat hK, isKGroupNative_hat hG ht hK.1,
    (pRank_hat K).trans hr, ⟨0, by simp⟩, Or.inl ⟨⊤, ?_⟩⟩
  have hfix : fixedSubgroup (Hat K) (1 : MulAut (Hat K)) = ⊤ := by
    ext x
    simp [fixedSubgroup]
  let e : ↥(fixedSubgroup (Hat K) (1 : MulAut (Hat K))) ≃* Hat K :=
    (MulEquiv.subgroupCongr hfix).trans Subgroup.topEquiv
  have hq : IsQuasisimple ↥(fixedSubgroup (Hat K) (1 : MulAut (Hat K))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (TwoThin.isQuasisimple_hat hK)
  have hc : pPrimeCore 2 ↥(fixedSubgroup (Hat K) (1 : MulAut (Hat K))) = ⊥ := by
    have h2 := pPrimeCore_map_iso 2 e
    rw [pPrimeCore_quotient_eq_bot K] at h2
    exact Subgroup.map_injective e.injective (h2.trans (Subgroup.map_bot _).symm)
  exact isPComponent_top hq hc

end CFSG.GH74.GLS.Stage1.Thm2.Recip
