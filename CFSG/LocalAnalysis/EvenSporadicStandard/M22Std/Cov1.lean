module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {L : Subgroup G}

structure CoverSetting (L : Subgroup G) (t : G) : Prop where
  orderOf_t : orderOf t = 2
  map_center : (center L).map L.subtype = zpowers t
  centralizer_L : centralizer (L : Set G) = zpowers t
  centralizer_t : centralizer ({t} : Set G) = normalizer (L : Set G)
  relIndex_dvd : L.relIndex (centralizer ({t} : Set G)) ∣ 2

namespace CoverSetting

variable {t : G}

theorem t_mem (hc : CoverSetting L t) : t ∈ L := by
  have : t ∈ (center L).map L.subtype := hc.map_center ▸ mem_zpowers t
  obtain ⟨z, -, rfl⟩ := this
  exact z.2

theorem t_mem_centralizer (hc : CoverSetting L t) : t ∈ centralizer (L : Set G) :=
  hc.centralizer_L ▸ mem_zpowers t

theorem le_centralizer (hc : CoverSetting L t) : L ≤ centralizer ({t} : Set G) := fun l hl =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hc.t_mem_centralizer l hl)

theorem mul_self_t (hc : CoverSetting L t) : t * t = 1 := by
  rw [← sq, ← hc.orderOf_t]
  exact pow_orderOf_eq_one t

theorem t_ne_one (hc : CoverSetting L t) : t ≠ 1 := by
  intro h
  have := hc.orderOf_t
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

end CoverSetting

variable [Finite G]

theorem exists_coverSetting
    (h25 : Finkelstein77.Asc76Lemma25) (h : StdHyp G L)
    (hq : IsSporadic (L ⧸ center L) .M22) (hZ : center L ≠ ⊥) : ∃ t : G, CoverSetting L t := by
  have hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2 := fun S =>
    Finkelstein77.card_sylow_eq_two_of_rowData h (HypOne.M22.rowData_of_isSporadic hq) h25 S
  obtain ⟨t, ht2, htZ, -, -, -, -, -, hCt⟩ :=
    EvenSmallLie.std_center_involution h.toStandardSetting hZ
  obtain ⟨hC, hZt⟩ := h.centralizer_eq_zpowers_of_mem_center hS ht2 htZ
  refine ⟨t, ht2, hZt, hC, hCt, ?_⟩
  have htC : t ∈ centralizer (L : Set G) := hC ▸ mem_zpowers t
  have htL : t ∈ L := by
    obtain ⟨z, -, rfl⟩ := htZ
    exact z.2
  have hdvd := h.relIndex_sup_zpowers_dvd hS htC ht2
  rw [sup_eq_left.2 (zpowers_le.2 htL)] at hdvd
  exact hdvd.trans (innAut_index_dvd_two hq)

omit [Finite G] in
theorem coverSetting_cases {t : G} (hc : CoverSetting L t) :
    centralizer ({t} : Set G) = L ∨
      (L.relIndex (centralizer ({t} : Set G)) = 2 ∧
        ∀ y ∈ centralizer ({t} : Set G), y ∉ L → orderOf y ≠ 2) ∨
      (L.relIndex (centralizer ({t} : Set G)) = 2 ∧
        ∃ y ∈ centralizer ({t} : Set G), y ∉ L ∧ orderOf y = 2) := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hc.relIndex_dvd with h1 | h2
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hc.le_centralizer
  · right
    by_cases hy : ∃ y ∈ centralizer ({t} : Set G), y ∉ L ∧ orderOf y = 2
    · exact Or.inr ⟨h2, hy⟩
    · refine Or.inl ⟨h2, fun y hyC hyL hy2 => hy ⟨y, hyC, hyL, hy2⟩⟩

end CFSG.EvenSporadicStandard.M22Std
