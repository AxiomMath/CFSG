module

public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.Timmesfeld.FStar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DWTim79

open Subgroup CFSG.Open CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

theorem isExtraspecialPGroup_iff_isExtraspecial2 {G : Type} [Group G] [Finite G]
    (Q : Subgroup G) :
    IsExtraspecialPGroup 2 ↥Q ↔ IsExtraspecial2 Q := by
  constructor
  · rintro ⟨hP, hcomm, -, hcard⟩
    refine ⟨hP, ?_, ?_⟩
    · rw [← Subgroup.map_subtype_commutator Q, hcomm]
    · rw [← Subgroup.map_subtype_commutator Q, hcomm,
        Subgroup.card_map_of_injective Q.subtype_injective]
      exact hcard
  · rintro ⟨hP, hcomm, hcard⟩
    have hcomm' : commutator ↥Q = center ↥Q := by
      refine Subgroup.map_injective (f := Q.subtype) Q.subtype_injective ?_
      rw [Subgroup.map_subtype_commutator]
      exact hcomm
    have hcard' : Nat.card (center ↥Q) = 2 := by
      rw [← Subgroup.card_map_of_injective (K := center ↥Q) Q.subtype_injective, ← hcomm]
      exact hcard
    refine ⟨hP, hcomm', ?_, hcard'⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (IsPGroup 2 ↥Q) := ⟨hP⟩
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (hx | ⟨y, rfl⟩)
      · rw [← hcomm']
        exact hx
      · exact CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed.sq_mem_center
          (le_of_eq hcomm')
          (fun z hz => by
            have h := CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed.pow_two_eq_one_of_card_eq_two
              hcard' (⟨z, hz⟩ : center ↥Q)
            simpa using congrArg Subtype.val h) y
    · rw [← hcomm']
      intro x hx
      exact Subgroup.subset_closure (Or.inl hx)

theorem timmesfeldIsExtraspecial_iff_isExtraspecialPGroup (P : Type*) [Group P] :
    timmesfeldIsExtraspecial P ↔ IsExtraspecialPGroup 2 P :=
  ⟨fun h => ⟨h.1, h.2.1.trans h.2.2.1, h.2.2.1, h.2.2.2⟩,
    fun h => ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.1, h.2.2.2⟩⟩

theorem isExtraspecialPGroup_map_iff {H G : Type*} [Group H] [Group G] {p : ℕ}
    (K : Subgroup H) (f : H →* G) (hf : Function.Injective f) :
    IsExtraspecialPGroup p ↥(K.map f) ↔ IsExtraspecialPGroup p ↥K :=
  ⟨fun h => isExtraspecialPGroup_of_mulEquiv
      (Subgroup.equivMapOfInjective K f hf).symm h,
    fun h => isExtraspecialPGroup_of_mulEquiv (Subgroup.equivMapOfInjective K f hf) h⟩

theorem timmesfeldIsExtraspecial_of_isExtraspecial2_map {H G : Type} [Group H] [Group G]
    [Finite G] (K : Subgroup H) (f : H →* G) (hf : Function.Injective f)
    (h : IsExtraspecial2 (K.map f)) : timmesfeldIsExtraspecial K :=
  (timmesfeldIsExtraspecial_iff_isExtraspecialPGroup K).mpr <|
    (isExtraspecialPGroup_map_iff K f hf).mp <|
      (isExtraspecialPGroup_iff_isExtraspecial2 (K.map f)).mpr h

theorem Qa_eq_map_generalizedFitting {G : Type} [Group G] (a : G) :
    Qa a = (CFSG.generalizedFitting (centralizer ({a} : Set G))).map
      (centralizer ({a} : Set G)).subtype := rfl

@[expose] noncomputable def settingOfQa {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) (hext : IsExtraspecial2 (Qa z)) : Setting G :=
  Setting.ofFStar z hz <| by
    rw [← CFSG.LargeExtraspecial.Bridge.generalizedFitting_eq_timmesfeldFStar]
    refine timmesfeldIsExtraspecial_of_isExtraspecial2_map
      (CFSG.generalizedFitting (centralizer ({z} : Set G)))
      (centralizer ({z} : Set G)).subtype
      (centralizer ({z} : Set G)).subtype_injective ?_
    simpa only [Qa, fStar] using hext

@[simp] theorem settingOfQa_z {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) (hext : IsExtraspecial2 (Qa z)) :
    (settingOfQa hz hext).z = z := rfl

@[simp] theorem settingOfQa_QG {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) (hext : IsExtraspecial2 (Qa z)) :
    (settingOfQa hz hext).QG = Qa z := by
  change (timmesfeldFStar (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = Qa z
  rw [Qa_eq_map_generalizedFitting,
    ← CFSG.LargeExtraspecial.Bridge.generalizedFitting_eq_timmesfeldFStar]

end CFSG.LargeExtraspecial.DWTim79
