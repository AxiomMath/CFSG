module

public import CFSG.LocalAnalysis.EvenSmallLie.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.OddCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open

section StdHypLemmas

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem StdHyp.centralizer_le_normalizer (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard h.standard ht ht2

theorem StdHyp.exists_involution_centralizer (h : StdHyp G L) :
    ∃ t : G, t ∈ centralizer (L : Set G) ∧ orderOf t = 2 := by
  exact CFSG.Open.standardComponentIsStandard.exists_involution_centralizer h.standard

theorem StdHyp.ne_top (h : StdHyp G L) : L ≠ ⊤ := by
  exact CFSG.Open.standardComponentIsStandard.ne_top h.standard h.simple h.nonabelian

theorem StdHyp.centralizer_le_normalizer_centralizer (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) := by
  obtain ⟨-, -, -, hN, -⟩ := h.standard
  rw [hN]
  exact h.centralizer_le_normalizer ht ht2

theorem centralizer_isComplement'
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (CFSG.pPrimeCore 2 (centralizer (L : Set G))).IsComplement'
      (zpowers (⟨t, ht⟩ : centralizer (L : Set G))) :=
  isComplement'_pPrimeCore_zpowers hS (by rw [Subgroup.orderOf_mk]; exact ht2)

theorem StdHyp.exists_cyclic_sylow_mem (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    ∃ S : Sylow 2 (centralizer (L : Set G)), IsCyclic S ∧
      (⟨t, ht⟩ : centralizer (L : Set G)) ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht₀ : orderOf (⟨t, ht⟩ : centralizer (L : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht2
  obtain ⟨S, hS⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, ht₀, pow_one]) :
      IsPGroup 2 (zpowers (⟨t, ht⟩ : centralizer (L : Set G)))).exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := h.cyclicSylow
  let f : S₀ ≃* S := Sylow.equiv S₀ S
  exact ⟨S, isCyclic_of_surjective f.toMonoidHom f.surjective, hS (mem_zpowers _)⟩

theorem StdHyp.centralizer_inf_centralizer_eq_map_sylow (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S)
    (htS : (⟨t, ht⟩ : centralizer (L : Set G)) ∈ S) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) =
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype :=
  inf_centralizer_singleton_eq_map_sylow ht (h.centralizer_le_normalizer_centralizer ht ht2)
    (h.oddCore t ht2) S hS htS

theorem StdHyp.centralizer_inf_centralizer_eq_zpowers (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_singleton_eq_zpowers ht ht2 (h.centralizer_le_normalizer_centralizer ht ht2)
    (h.oddCore t ht2) hS

theorem StdHyp.centralizer_inf_sup_centralizer_eq (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ⊓ (L ⊔ centralizer (L : Set G)) = L ⊔ zpowers t := by
  rw [centralizer_singleton_inf_sup_centralizer ht,
    h.centralizer_inf_centralizer_eq_zpowers hS ht ht2]

theorem StdHyp.centralizer_eq_sup_zpowers (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    centralizer ({t} : Set G) = L ⊔ zpowers t := by
  rw [← h.centralizer_inf_sup_centralizer_eq hS ht ht2, inf_eq_left.2 hinn]

theorem StdHyp.centralizer_eq_sup_map_sylow (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S)
    (htS : (⟨t, ht⟩ : centralizer (L : Set G)) ∈ S)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    centralizer ({t} : Set G) =
      L ⊔ (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := by
  rw [centralizer_singleton_eq_sup_inf ht hinn,
    h.centralizer_inf_centralizer_eq_map_sylow ht ht2 S hS htS]

theorem StdHyp.relIndex_sup_centralizer_dvd (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (L ⊔ centralizer (L : Set G)).relIndex (centralizer ({t} : Set G)) ∣
      (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index := by
  have hMN := h.centralizer_le_normalizer ht ht2
  have hsub : (L ⊔ centralizer (L : Set G)).subgroupOf (centralizer ({t} : Set G)) =
      (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.comap
        ((normalizerAction L).comp (Subgroup.inclusion hMN)) := by
    ext g
    exact (normalizerAction_mem_range_conj_iff h.standard.1.1 (Subgroup.inclusion hMN g)).symm
  have hnorm := normal_range_conj (L ⧸ center L)
  rw [Subgroup.relIndex, hsub, Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem StdHyp.relIndex_sup_zpowers_dvd (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣
      (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index := by
  rw [← h.centralizer_inf_sup_centralizer_eq hS ht ht2, Subgroup.inf_relIndex_left]
  exact h.relIndex_sup_centralizer_dvd ht ht2

theorem StdHyp.centralizer_le_sup_centralizer_of_mulAut_inner (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hinner : ∀ α : MulAut L, ∃ l : L, α = MulAut.conj l) :
    centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
  (h.centralizer_le_normalizer ht ht2).trans (normalizer_le_sup_centralizer_of_mulAut_inner hinner)

theorem StdHyp.centralizer_le_sup_centralizer_of_inner (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hinner : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) :
    centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
  h.centralizer_le_sup_centralizer_of_mulAut_inner ht ht2
    (mulAut_inner_of_inner_centerQuotient h.standard.1.1 hinner)

theorem StdHyp.centralizer_eq_prod_of_center_eq_bot (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) (hZ : center L = ⊥) :
    centralizer ({t} : Set G) = L ⊔ zpowers t ∧ Disjoint L (zpowers t) ∧
      zpowers t ≤ centralizer (L : Set G) := by
  exact ⟨h.centralizer_eq_sup_zpowers hS ht ht2 hinn,
    disjoint_of_le_centralizer_of_center_eq_bot (zpowers_le.2 ht) hZ, zpowers_le.2 ht⟩

theorem StdHyp.nonempty_mulEquiv_prod_of_center_eq_bot (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) (hZ : center L = ⊥) :
    Nonempty (centralizer ({t} : Set G) ≃* L × zpowers t) := by
  obtain ⟨hC, hd, hcomm⟩ := h.centralizer_eq_prod_of_center_eq_bot hS ht ht2 hinn hZ
  exact ⟨(MulEquiv.subgroupCongr hC).trans (mulEquivProdSup hcomm hd).symm⟩

theorem StdHyp.centralizer_eq_zpowers_of_mem_center (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht2 : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype) :
    centralizer (L : Set G) = zpowers t ∧ (center L).map L.subtype = zpowers t := by
  have htC : t ∈ centralizer (L : Set G) := ((map_center_eq_inf_centralizer L) ▸ htZ).2
  have htL : t ∈ L := ((map_center_eq_inf_centralizer L) ▸ htZ).1
  have hCH : centralizer (L : Set G) ≤ centralizer ({t} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hc) t htL).symm
  have hC : centralizer (L : Set G) = zpowers t := by
    have := h.centralizer_inf_centralizer_eq_zpowers hS htC ht2
    rwa [inf_eq_left.2 hCH] at this
  refine ⟨hC, ?_⟩
  rw [map_center_eq_inf_centralizer, hC]
  exact inf_eq_right.2 (zpowers_le.2 htL)

theorem StdHyp.centralizer_eq_of_mem_center (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht2 : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    centralizer ({t} : Set G) = L := by
  have htC : t ∈ centralizer (L : Set G) := ((map_center_eq_inf_centralizer L) ▸ htZ).2
  have htL : t ∈ L := ((map_center_eq_inf_centralizer L) ▸ htZ).1
  rw [h.centralizer_eq_sup_zpowers hS htC ht2 hinn]
  exact sup_eq_left.2 (zpowers_le.2 htL)

theorem StdHyp.exists_standard_form_of_inner (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hZ : Nat.card (center L) = 2)
    (hinner : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) :
    ∃ t : G, orderOf t = 2 ∧ (center L).map L.subtype = zpowers t ∧
      centralizer (L : Set G) = zpowers t ∧ centralizer ({t} : Set G) = L := by
  obtain ⟨z, hz, hZz⟩ := exists_map_center_eq_zpowers hZ
  have hzZ : z ∈ (center L).map L.subtype := hZz ▸ mem_zpowers z
  have hzC : z ∈ centralizer (L : Set G) := ((map_center_eq_inf_centralizer L) ▸ hzZ).2
  exact ⟨z, hz, hZz, (h.centralizer_eq_zpowers_of_mem_center hS hz hzZ).1,
    h.centralizer_eq_of_mem_center hS hz hzZ
      (h.centralizer_le_sup_centralizer_of_inner hzC hz hinner)⟩

end StdHypLemmas

end CFSG.EvenSporadicStandard
