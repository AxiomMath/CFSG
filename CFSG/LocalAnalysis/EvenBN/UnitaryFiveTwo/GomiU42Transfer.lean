module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Transport

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {t : G}

private theorem subtype_conj_comp (ht : t ∈ Bs) :
    Bs.subtype.comp (MulAut.conj (⟨t, ht⟩ : ↥Bs)).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp Bs.subtype := by
  ext y
  simp [MulAut.conj_apply]

private theorem map_subtype_map_conj (ht : t ∈ Bs) (K : Subgroup ↥Bs) :
    (K.map (MulAut.conj (⟨t, ht⟩ : ↥Bs)).toMonoidHom).map Bs.subtype =
      (K.map Bs.subtype).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, subtype_conj_comp ht]

theorem layer_transfer (ht : t ∈ Bs) {J₀ : Subgroup G} (hJ₀ : J₀ ≤ Bs)
    (hI : CFSG.layer ↥Bs ⊓ centralizer ({(⟨t, ht⟩ : ↥Bs)} : Set ↥Bs) = J₀.subgroupOf Bs)
    (hdisj : CFSG.Blueprint.LieModel ↥(CFSG.layer ↥Bs) .PSL 4 2 2 ∨
      ∃ K₀ : Subgroup ↥Bs, CFSG.Blueprint.LieModel ↥K₀ .PSU 4 2 1 ∧
        CFSG.layer ↥Bs = K₀ ⊔ K₀.map (MulAut.conj (⟨t, ht⟩ : ↥Bs)).toMonoidHom ∧
        ⁅K₀, K₀.map (MulAut.conj (⟨t, ht⟩ : ↥Bs)).toMonoidHom⁆ = ⊥ ∧
        K₀ ⊓ K₀.map (MulAut.conj (⟨t, ht⟩ : ↥Bs)).toMonoidHom = ⊥) :
    (CFSG.layer ↥Bs).map Bs.subtype ⊓ centralizer ({t} : Set G) = J₀ ∧
      (CFSG.Blueprint.LieModel ↥((CFSG.layer ↥Bs).map Bs.subtype) .PSL 4 2 2 ∨
        ∃ K₀ : Subgroup G, CFSG.Blueprint.LieModel ↥K₀ .PSU 4 2 1 ∧
          (CFSG.layer ↥Bs).map Bs.subtype = K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom ∧
          ⁅K₀, K₀.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
          K₀ ⊓ K₀.map (MulAut.conj t).toMonoidHom = ⊥) := by
  have hinj : Function.Injective Bs.subtype := Bs.subtype_injective
  have hpart1 : (CFSG.layer ↥Bs).map Bs.subtype ⊓ centralizer ({t} : Set G) = J₀ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨y, hyL, rfl⟩ := Subgroup.mem_map.mp hxL
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC
      have hyC : y ∈ centralizer ({(⟨t, ht⟩ : ↥Bs)} : Set ↥Bs) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext hxC
      have hy : y ∈ J₀.subgroupOf Bs := by
        rw [← hI]
        exact Subgroup.mem_inf.mpr ⟨hyL, hyC⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      have hy : (⟨x, hJ₀ hx⟩ : ↥Bs) ∈ J₀.subgroupOf Bs := Subgroup.mem_subgroupOf.mpr hx
      rw [← hI, Subgroup.mem_inf] at hy
      obtain ⟨hyL, hyC⟩ := hy
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨⟨x, hJ₀ hx⟩, hyL, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      have h := congrArg Subtype.val hyC
      simpa using h
  refine ⟨hpart1, ?_⟩
  rcases hdisj with hL | ⟨K₀, hK₀, hsup, hcomm, hint⟩
  · left
    exact lieModel_of_mulEquiv_classical
      (Subgroup.equivMapOfInjective (CFSG.layer ↥Bs) Bs.subtype hinj).symm (by decide) hL
  · right
    refine ⟨K₀.map Bs.subtype, ?_, ?_, ?_, ?_⟩
    · exact lieModel_of_mulEquiv_classical
        (Subgroup.equivMapOfInjective K₀ Bs.subtype hinj).symm (by decide) hK₀
    · rw [hsup, Subgroup.map_sup, map_subtype_map_conj ht K₀]
    · rw [← map_subtype_map_conj ht K₀, ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
    · rw [← map_subtype_map_conj ht K₀, ← Subgroup.map_inf _ _ _ hinj, hint, Subgroup.map_bot]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
