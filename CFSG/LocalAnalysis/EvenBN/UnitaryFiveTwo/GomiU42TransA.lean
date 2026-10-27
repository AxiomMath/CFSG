module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Transport

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] {Bs : Subgroup G} {e t : G} {J₀ : Subgroup G}

private theorem gomiTA_zpowers_subgroupOf {g : G} (hg : g ∈ Bs) :
    zpowers (⟨g, hg⟩ : ↥Bs) = (zpowers g).subgroupOf Bs := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem gomiTA_inf_subgroupOf (A C : Subgroup G) :
    (A ⊓ C).subgroupOf Bs = A.subgroupOf Bs ⊓ C.subgroupOf Bs :=
  Subgroup.comap_inf A C Bs.subtype

private theorem gomiTA_centralizer_subgroupOf {g : G} (hg : g ∈ Bs) :
    centralizer ({(⟨g, hg⟩ : ↥Bs)} : Set ↥Bs) =
      (centralizer ({g} : Set G)).subgroupOf Bs := by
  ext x
  simp [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subtype.ext_iff]

theorem lieModel_subgroupOf_PSU (hJ : J₀ ≤ Bs) (h : CFSG.Blueprint.LieModel ↥J₀ .PSU 4 2 1) :
    CFSG.Blueprint.LieModel ↥(J₀.subgroupOf Bs) .PSU 4 2 1 :=
  lieModel_of_mulEquiv_classical (Subgroup.subgroupOfEquivOfLe hJ) (by decide) h

theorem inf_e_subgroupOf (he : e ∈ Bs) (hJ : J₀ ≤ Bs) (h : zpowers e ⊓ J₀ = ⊥) :
    zpowers (⟨e, he⟩ : ↥Bs) ⊓ J₀.subgroupOf Bs = ⊥ := by
  rw [gomiTA_zpowers_subgroupOf he, ← gomiTA_inf_subgroupOf, h, Subgroup.bot_subgroupOf]

theorem centralizer_eq_subgroupOf (he : e ∈ Bs) (ht : t ∈ Bs) (hJ : J₀ ≤ Bs)
    (h : Bs ⊓ centralizer ({t} : Set G) = zpowers t ⊔ (zpowers e ⊔ J₀)) :
    centralizer ({(⟨t, ht⟩ : ↥Bs)} : Set ↥Bs) =
      zpowers (⟨t, ht⟩ : ↥Bs) ⊔ (zpowers (⟨e, he⟩ : ↥Bs) ⊔ J₀.subgroupOf Bs) := by
  rw [gomiTA_centralizer_subgroupOf ht,
    ← Subgroup.inf_subgroupOf_left (centralizer ({t} : Set G)) Bs, h,
    Subgroup.subgroupOf_sup (Subgroup.zpowers_le.2 ht) (sup_le (Subgroup.zpowers_le.2 he) hJ),
    Subgroup.subgroupOf_sup (Subgroup.zpowers_le.2 he) hJ, gomiTA_zpowers_subgroupOf ht,
    gomiTA_zpowers_subgroupOf he]

theorem inf_t_subgroupOf (he : e ∈ Bs) (ht : t ∈ Bs) (hJ : J₀ ≤ Bs)
    (h : zpowers t ⊓ (zpowers e ⊔ J₀) = ⊥) :
    zpowers (⟨t, ht⟩ : ↥Bs) ⊓ (zpowers (⟨e, he⟩ : ↥Bs) ⊔ J₀.subgroupOf Bs) = ⊥ := by
  rw [gomiTA_zpowers_subgroupOf ht, gomiTA_zpowers_subgroupOf he,
    ← Subgroup.subgroupOf_sup (Subgroup.zpowers_le.2 he) hJ, ← gomiTA_inf_subgroupOf, h,
    Subgroup.bot_subgroupOf]

theorem le_centralizer_subgroupOf (ht : t ∈ Bs) (h : J₀ ≤ centralizer ({t} : Set G)) :
    J₀.subgroupOf Bs ≤ centralizer ({(⟨t, ht⟩ : ↥Bs)} : Set ↥Bs) := by
  rw [gomiTA_centralizer_subgroupOf ht]
  exact Subgroup.subgroupOf_mono Bs h

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
