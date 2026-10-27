module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2P61Obs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Th2.Bal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_pComponent_of_Z {u t : G} (ht2 : orderOf t = 2)
    (hut : u * t = t * u) {Z : Subgroup G}
    (hZt : Z ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)))
    (hZu : Z ≤ centralizer ({u} : Set G))
    (hZnot : ¬ Z ≤ pPrimeCoreOf 2 (centralizer ({u} : Set G))) :
    ∃ J : Subgroup G, IsPCompIn 2 (centralizer ({u} : Set G)) J ∧ t ∈ normalizer (J : Set G) ∧
      Z ≤ normalizer (J : Set G) ∧ t ∉ centralizerSection J (pPrimeCoreOf 2 J) ∧
      ¬ Z ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({u} : Set G) with hH
  have htsq : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have htH : t ∈ H := mem_centralizer_singleton_iff.2 hut.symm
  set D : Subgroup G := zpowers t with hD
  have hDH : D ≤ H := zpowers_le.2 htH
  have hDcard : 2 ^ 1 ≤ Nat.card D := by
    rw [hD, Nat.card_zpowers, ht2]
    norm_num
  have hD2 : ∀ d ∈ D, d * d = 1 := by
    intro d hd
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hd
    rw [← zpow_add, ← two_mul, zpow_mul]
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htsq
    rw [h2, one_zpow]
  set Y : Subgroup G := pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ H with hY
  have hYd : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) := by
    intro d hd hd1
    rcases mem_zpowers_two ht2 hd with h0 | h0
    · exact absurd h0 hd1
    · rw [h0]
      exact inf_le_left
  have hZY : Z ≤ Y := le_inf hZt hZu
  set N : Subgroup (CentralizerBar u) := (Z.subgroupOf H).map (piBar u) with hN
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hZnot
    intro z hz
    have hzH : z ∈ H := hZu hz
    have hmem : piBar u ⟨z, hzH⟩ ∈ N := ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
    exact ⟨⟨z, hzH⟩, hmem, rfl⟩
  have hNY : N ≤ (Y.subgroupOf H).map (piBar u) :=
    Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.2 (hZY (Subgroup.mem_subgroupOf.1 hz)))
  obtain ⟨L, hL, hFL, hFfaith, hNL, hNnc, -⟩ :=
    exists_component_of_image (k := 1) le_rfl hDH hDcard hD2 hYd hNY hN1
  obtain ⟨J₀, hJ₀, hJ₀map⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hL
  set J : Subgroup G := J₀.map H.subtype with hJdef
  have hJH : J ≤ H := Subgroup.map_subtype_le J₀
  have hJsub : J.subgroupOf H = J₀ :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) J₀
  have hJc : IsPCompIn 2 H J := ⟨hJH, by rw [hJsub]; exact hJ₀⟩
  have hLJ : (J.subgroupOf H).map (piBar u) = L := by rw [hJsub]; exact hJ₀map
  refine ⟨J, hJc, ?_, ?_, ?_, ?_⟩
  · have hF : piBar u (⟨t, htH⟩ : ↥H) ∈ (D.subgroupOf H).map (piBar u) :=
      ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.2 (mem_zpowers t), rfl⟩
    exact mem_normalizer_of_piBar hJc hLJ htH (hFL _ hF)
  · intro z hz
    have hzH : z ∈ H := hZu hz
    have hzN : piBar u ⟨z, hzH⟩ ∈ N := ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    exact mem_normalizer_of_piBar hJc hLJ hzH (hNL _ hzN)
  · intro hts
    have hF : piBar u (⟨t, htH⟩ : ↥H) ∈ (D.subgroupOf H).map (piBar u) :=
      ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.2 (mem_zpowers t), rfl⟩
    have hne : piBar u (⟨t, htH⟩ : ↥H) ≠ 1 := by
      intro h1
      rw [piBar_eq_one_iff] at h1
      have hsq : (⟨t, htH⟩ : ↥H) * ⟨t, htH⟩ = 1 := Subtype.ext htsq
      exact ht1 (congrArg Subtype.val (eq_one_of_sq_of_mem_pPrimeCore hsq h1))
    exact hFfaith _ hF hne (piBar_centralizes_of_mem_cSec hJc hLJ htH hts)
  · intro hZs
    apply hNnc
    intro n hn x hx
    obtain ⟨z, hz, rfl⟩ := hn
    have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.1 hz
    exact piBar_centralizes_of_mem_cSec hJc hLJ z.2 (hZs hzZ) x hx

end CFSG.GH74.GLS.Th2.Obs
