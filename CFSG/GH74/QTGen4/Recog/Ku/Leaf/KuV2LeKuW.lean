module

public import CFSG.GH74.QTGen4.Recog.Ku.HGlueD
public import CFSG.GH74.QTGen4.Recog.Ku.RStructH
public import CFSG.GH74.QTGen4.Recog.Ku.RStructI

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

def leafHom (h : KuHyp G T M H P z) {r : G} (hr : r ∈ kuR T M) :
    ↥(pCoreOf 2 M) →* ↥(kuV2 T M) where
  toFun v := ⟨r⁻¹ * (v : G) * r * (v : G)⁻¹, inv_conj_mul_inv_mem_kuV2 h hr v⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    have hrN : r ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := h.kuR_normalizer hr
    have hcx : ∀ x : ↥(pCoreOf 2 M), r⁻¹ * (x : G) * r ∈ pCoreOf 2 M := by
      intro x
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) (x : G)).mp x.2
      simpa using this
    have hxy : (b : G)⁻¹ * (a : G)⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ := by
      have ha' : (a : G)⁻¹ ∈ pCoreOf 2 M := (pCoreOf 2 M).inv_mem a.2
      have hb' : (b : G)⁻¹ ∈ pCoreOf 2 M := (pCoreOf 2 M).inv_mem b.2
      exact comm_of_mem_pCoreOf h hb' ha'
    have hcy : (r⁻¹ * (b : G) * r) * (a : G)⁻¹ = (a : G)⁻¹ * (r⁻¹ * (b : G) * r) :=
      comm_of_mem_pCoreOf h (hcx b) ((pCoreOf 2 M).inv_mem a.2)
    show r⁻¹ * ((a : G) * (b : G)) * r * ((a : G) * (b : G))⁻¹ =
      (r⁻¹ * (a : G) * r * (a : G)⁻¹) * (r⁻¹ * (b : G) * r * (b : G)⁻¹)
    have e1 : r⁻¹ * ((a : G) * (b : G)) * r * ((a : G) * (b : G))⁻¹ =
        (r⁻¹ * (a : G) * r) * (r⁻¹ * (b : G) * r) * ((b : G)⁻¹ * (a : G)⁻¹) := by
      group
    rw [e1, hxy]
    calc (r⁻¹ * (a : G) * r) * (r⁻¹ * (b : G) * r) * ((a : G)⁻¹ * (b : G)⁻¹)
        = (r⁻¹ * (a : G) * r) * ((r⁻¹ * (b : G) * r) * (a : G)⁻¹) * (b : G)⁻¹ := by group
      _ = (r⁻¹ * (a : G) * r) * ((a : G)⁻¹ * (r⁻¹ * (b : G) * r)) * (b : G)⁻¹ := by rw [hcy]
      _ = (r⁻¹ * (a : G) * r * (a : G)⁻¹) * (r⁻¹ * (b : G) * r * (b : G)⁻¹) := by group

theorem ker_leafHom (h : KuHyp G T M H P z) {r : G} (hr : r ∈ kuR T M)
    (hrV : r ∉ pCoreOf 2 M) :
    (leafHom h hr).ker = (kuV2 T M).subgroupOf (pCoreOf 2 M) := by
  ext v
  have hC : ∀ g : G, g ∈ kuV2 T M ↔ g ∈ pCoreOf 2 M ∧ r * g = g * r := by
    intro g
    rw [← h.centralizer_pCore_eq_kuV2 hr hrV]
    constructor
    · rintro ⟨hgV, hgC⟩
      refine ⟨hgV, ?_⟩
      exact Subgroup.mem_centralizer_iff.mp hgC r (Set.mem_singleton r)
    · rintro ⟨hgV, hgc⟩
      refine ⟨hgV, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        exact hgc
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hC]
  constructor
  · intro hv
    have hv' : r⁻¹ * (v : G) * r * (v : G)⁻¹ = 1 := congrArg Subtype.val hv
    refine ⟨v.2, ?_⟩
    have : r⁻¹ * (v : G) * r = (v : G) := by
      calc r⁻¹ * (v : G) * r = r⁻¹ * (v : G) * r * (v : G)⁻¹ * (v : G) := by group
        _ = (v : G) := by rw [hv', one_mul]
    calc r * (v : G) = r * (r⁻¹ * (v : G) * r) := by rw [this]
      _ = (v : G) * r := by group
  · rintro ⟨-, hc⟩
    apply Subtype.ext
    show r⁻¹ * (v : G) * r * (v : G)⁻¹ = 1
    have : r⁻¹ * (v : G) * r = (v : G) := by
      calc r⁻¹ * (v : G) * r = r⁻¹ * ((v : G) * r) := by group
        _ = r⁻¹ * (r * (v : G)) := by rw [hc]
        _ = (v : G) := by group
    rw [this]
    group

theorem leafHom_surjective (h : KuHyp G T M H P z) {r : G} (hr : r ∈ kuR T M)
    (hrV : r ∉ pCoreOf 2 M) : Function.Surjective (leafHom h hr) := by
  rw [← MonoidHom.range_eq_top]
  have hle : kuV2 T M ≤ pCoreOf 2 M := inf_le_left
  have hV : Nat.card (pCoreOf 2 M) = 16 := h.vCard
  have hK : Nat.card ((leafHom h hr).ker) = 4 := by
    rw [ker_leafHom h hr hrV,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, h.card_kuV2]
  have hmain := Subgroup.card_eq_card_quotient_mul_card_subgroup (leafHom h hr).ker
  have hq := Nat.card_congr (QuotientGroup.quotientKerEquivRange (leafHom h hr)).toEquiv
  rw [hK, hV] at hmain
  have hR : Nat.card (leafHom h hr).range = 4 := by
    rw [← hq]
    omega
  apply Subgroup.eq_top_of_card_eq
  rw [hR, h.card_kuV2]

theorem kuV2_le_P [KuLeaf LeafEqKuAOfElemAbelian] (h : KuHyp G T M H P z) : kuV2 T M ≤ P := by
  have hRP : 16 ≤ Nat.card ↥(kuR T M ⊓ P) := by
    have h1 := Subgroup.relIndex_mul_card (H := kuR T M) (K := P)
    rw [h.card_P] at h1
    have h2 : (kuR T M).relIndex P ≤ 2 := by
      have h3 := Subgroup.relIndex_le_of_le_right h.P_le_T
        (show (kuR T M).relIndex T ≠ 0 by rw [h.relIndex_kuR]; norm_num)
      rwa [h.relIndex_kuR] at h3
    have h4 : (kuR T M).relIndex P * Nat.card ↥(kuR T M ⊓ P) ≤
        2 * Nat.card ↥(kuR T M ⊓ P) := Nat.mul_le_mul_right _ h2
    have h5 : 32 ≤ 2 * Nat.card ↥(kuR T M ⊓ P) := h1.symm.le.trans h4
    omega
  obtain ⟨p, hpR, hpP, hpV⟩ : ∃ p ∈ kuR T M, p ∈ P ∧ p ∉ pCoreOf 2 M := by
    by_contra hc
    have hsub : kuR T M ⊓ P ≤ pCoreOf 2 M ⊓ P := by
      intro x hx
      refine ⟨?_, hx.2⟩
      by_contra hxV
      exact hc ⟨x, hx.1, hx.2, hxV⟩
    have h1 := Subgroup.card_le_of_le hsub
    have h2 := h.card_pCore_M_inf_P
    omega
  intro x hx
  obtain ⟨v, hv⟩ := leafHom_surjective h hpR hpV ⟨x, hx⟩
  have hval : p⁻¹ * (v : G) * p * (v : G)⁻¹ = x := congrArg Subtype.val hv
  have hvN : (v : G) ∈ Subgroup.normalizer (P : Set G) :=
    h.hNormP (h.tH (h.pCore_le_T v.2))
  have hconj : (v : G) * p * (v : G)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hvN p).mp hpP
  rw [← hval, show p⁻¹ * (v : G) * p * (v : G)⁻¹ = p⁻¹ * ((v : G) * p * (v : G)⁻¹) by group]
  exact P.mul_mem (P.inv_mem hpP) hconj

theorem kuV2_le_kuW_core [KuLeaf LeafEqKuAOfElemAbelian] (h : KuHyp G T M H P z) :
    kuV2 T M ≤ kuW P H := by
  haveI := h.isEA_quot_P
  have hV2P : kuV2 T M ≤ P := h.kuV2_le_P
  obtain ⟨u, hu, hcos⟩ := h.exists_u_coset
  have hnu : u ∉ P := fun hup =>
    (hcos 1 (pCoreOf 2 H).one_mem).mp (by rwa [one_mul]) P.one_mem
  have huu : u * u ∈ P := (hcos u hu).mpr hnu
  have hun : u ∈ Subgroup.normalizer (P : Set G) :=
    h.hNormP (CFSG.LieType.BorelTits.pCoreOf_le 2 H hu)
  have huT : u ∈ T := h.pCore_H_le_T hu
  have hkW : Nat.card (LinearMap.range (kuDeltaLin (actV hun))) * 2 = 8 := by
    have h1 := h.card_kuW
    rw [kuW_eq_psiPre h hu hcos, card_psiPre, h.card_center_P] at h1
    exact h1
  have hcardR : Nat.card (LinearMap.range (kuDeltaLin (actV hun))) = 4 := by omega
  have hfinR : Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin (actV hun))) = 2 := by
    have e : Nat.card (LinearMap.range (kuDeltaLin (actV hun))) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin (actV hun))) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
    have e2 : (2 : ℕ) ^ Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin (actV hun))) =
        2 ^ 2 := by
      rw [← e, hcardR]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) e2
  have hfinV : Module.finrank (ZMod 2) (Additive (↥P ⧸ Subgroup.center ↥P)) = 4 :=
    h.finrank_quotP
  have hsum := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (kuDeltaLin (actV hun))
  have hγ : ∀ v, actV hun (actV hun v) = v := actV_involutive hun huu
  have hle : LinearMap.range (kuDeltaLin (actV hun)) ≤ LinearMap.ker (kuDeltaLin (actV hun)) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact kuDeltaLin_delta _ hγ v
  have hker : LinearMap.range (kuDeltaLin (actV hun)) = LinearMap.ker (kuDeltaLin (actV hun)) :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.zP_sq) h.z_ne_one
  have hzV2 : Subgroup.zpowers z ≤ kuV2 T M := Subgroup.zpowers_le.mpr h.z_mem_kuV2
  have hrel : (Subgroup.zpowers z).relIndex (kuV2 T M) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers z) (K := kuV2 T M)
    rw [inf_eq_left.mpr hzV2, Nat.card_zpowers, hzord, h.card_kuV2] at h1
    omega
  obtain ⟨g, hgV2, hg⟩ := Subgroup.relIndex_eq_two_iff.mp hrel
  have hE : ∀ b ∈ kuV2 T M, b * g ∈ Subgroup.zpowers z ∨ b ∈ Subgroup.zpowers z := by
    intro b hb
    rcases hg b hb with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hgz : g ∉ Subgroup.zpowers z := by
    intro hgz
    rcases hg 1 (kuV2 T M).one_mem with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2 (Subgroup.one_mem _)
    · exact h2 (by rw [one_mul]; exact hgz)
  have hgP : g ∈ P := hV2P hgV2
  have hcomm : u * z = z * u := (h.z_mem_center_T).2 u huT
  have mem_center_of : ∀ a : ↥P, (a : G) ∈ Subgroup.zpowers z → a ∈ Subgroup.center ↥P := by
    intro a ha
    rw [h.center_P_eq]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  have psi_zero_of_mem : ∀ a : ↥P, (a : G) ∈ Subgroup.zpowers z → psi a = 0 :=
    fun a ha => (psi_eq_zero_iff a).mpr (mem_center_of a ha)
  have psi_add_of_mul : ∀ a b : ↥P, (a : G) * (b : G) ∈ Subgroup.zpowers z →
      psi a + psi b = 0 := by
    intro a b hab
    rw [← psi_mul, psi_eq_zero_iff]
    exact mem_center_of _ (by rw [Subgroup.coe_mul]; exact hab)
  have hxV2 : u * g * u⁻¹ ∈ kuV2 T M :=
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_kuV2 huT) g).mp hgV2
  have hxP : u * g * u⁻¹ ∈ P := hV2P hxV2
  have hG : actV hun (psi (⟨g, hgP⟩ : ↥P)) = psi (⟨g, hgP⟩ : ↥P) := by
    rcases hE (u * g * u⁻¹) hxV2 with hxg | hxz
    · have h1 : psi (⟨u * g * u⁻¹, hxP⟩ : ↥P) + psi (⟨g, hgP⟩ : ↥P) = 0 :=
        psi_add_of_mul _ _ hxg
      have e : actV hun (psi (⟨g, hgP⟩ : ↥P)) = psi (⟨u * g * u⁻¹, hxP⟩ : ↥P) :=
        actV_mk hun (⟨g, hgP⟩ : ↥P)
      rw [e]
      exact (eq_of_add_eq_zero_V h1).symm
    · exfalso
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxz
      have hc : Commute u (z ^ n) := (show Commute u z from hcomm).zpow_right n
      apply hgz
      have hgn : g = z ^ n := by
        calc g = u⁻¹ * (u * g * u⁻¹) * u := by group
          _ = u⁻¹ * z ^ n * u := by rw [hn]
          _ = z ^ n := by rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
      rw [hgn]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) n
  have hfix : ∀ b (hb : b ∈ kuV2 T M),
      actV hun (psi (⟨b, hV2P hb⟩ : ↥P)) = psi (⟨b, hV2P hb⟩ : ↥P) := by
    intro b hb
    rcases hE b hb with hbg | hbz
    · have h1 : psi (⟨b, hV2P hb⟩ : ↥P) + psi (⟨g, hgP⟩ : ↥P) = 0 :=
        psi_add_of_mul _ _ hbg
      have h2 : psi (⟨b, hV2P hb⟩ : ↥P) = psi (⟨g, hgP⟩ : ↥P) :=
        (eq_of_add_eq_zero_V h1).symm
      rw [h2]
      exact hG
    · rw [psi_zero_of_mem (⟨b, hV2P hb⟩ : ↥P) hbz, map_zero]
  intro b hb
  have hmem : psi (⟨b, hV2P hb⟩ : ↥P) ∈ LinearMap.range (kuDeltaLin (actV hun)) := by
    rw [hker, LinearMap.mem_ker, kuDeltaLin_apply, hfix b hb, add_self_eq_zero_V]
  rw [kuW_eq_psiPre h hu hcos]
  exact mem_psiPre_iff.mpr ⟨hV2P hb, hmem⟩

end KuHyp

theorem leafKuV2LeKuW
    [KuLeaf LeafEqKuAOfElemAbelian]
    : LeafKuV2LeKuW := by
  intro G _ _ T M H P z h
  exact KuHyp.kuV2_le_kuW_core h


end CFSG.GH74.QTGen4.Ku
