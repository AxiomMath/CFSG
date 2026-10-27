module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.Foundations.MaxCardThompson

public section

namespace CFSG

variable {G : Type*} [Group G]

theorem thompsonAbelianSubgroups_top_eq_setOf_isMaxCardAbelian :
    thompsonAbelianSubgroups (⊤ : Subgroup G) = {A : Subgroup G | IsMaxCardAbelian A} :=
  ambientMaxCardAbelianFamily_top

theorem thompsonSubgroup_top_eq_maxCardThompson :
    thompsonSubgroup (⊤ : Subgroup G) = maxCardThompson G :=
  ambientMaxCardThompson_top

theorem map_subtype_mem_thompsonAbelianSubgroups {S : Subgroup G} {A : Subgroup S}
    (hA : IsMaxCardAbelian A) : A.map S.subtype ∈ thompsonAbelianSubgroups S :=
  map_subtype_mem_ambientMaxCardAbelianFamily hA

theorem exists_mem_thompsonAbelianSubgroups_of_finite (S : Subgroup G) [Finite S] :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups S := by
  obtain ⟨B, hB⟩ := thompsonAbelianSubgroups_nonempty (G := S) ⊤
  rw [thompsonAbelianSubgroups_top_eq_setOf_isMaxCardAbelian] at hB
  exact ⟨B.map S.subtype, map_subtype_mem_thompsonAbelianSubgroups hB⟩

theorem thompsonSubgroup_eq_map_maxCardThompson (S : Subgroup G) :
    thompsonSubgroup S = (maxCardThompson S).map S.subtype :=
  ambientMaxCardThompson_eq_map S

theorem centerIn_map_subtype (S : Subgroup G) (K : Subgroup S) :
    centerIn (K.map S.subtype) = ((Subgroup.center K).map K.subtype).map S.subtype :=
  by
  rw [center_map_subtype_eq_inf_centralizer]
  exact map_subtype_inf_centralizer_self S K

theorem thompsonCenter_top_eq_maxCardZJ :
    thompsonCenter (⊤ : Subgroup G) = maxCardZJ G :=
  ambientMaxCardZJ_top

theorem thompsonCenter_eq_map_maxCardZJ (S : Subgroup G) :
    thompsonCenter S = (maxCardZJ S).map S.subtype :=
  ambientMaxCardZJ_eq_map S

theorem normalizer_le_normalizer_thompsonSubgroup_of_bounded (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (thompsonSubgroup S : Set G) :=
  normalizer_le_normalizer_ambientMaxCardThompson S

theorem normalizer_le_normalizer_thompsonCenter_of_bounded (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (thompsonCenter S : Set G) :=
  normalizer_le_normalizer_ambientMaxCardZJ S

section Injective

variable {H : Type*} [Group H]

theorem map_thompsonSubgroup_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    (thompsonSubgroup S).map f = thompsonSubgroup (S.map f) :=
  map_ambientMaxCardThompson_of_injective f S hf

theorem map_thompsonCenter_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    (thompsonCenter S).map f = thompsonCenter (S.map f) :=
  map_ambientMaxCardZJ_of_injective f S hf

end Injective

end CFSG
