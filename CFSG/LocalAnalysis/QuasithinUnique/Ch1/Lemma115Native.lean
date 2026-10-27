module

public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.SectionRank CFSG.Milestones
  CFSG.QuasithinUnique

theorem sqtkSimpleList_iff (X : Type) [Group X] :
    SQTKSimpleList X ↔ AltList X ∨ OddList X ∨ SQTKCharTwoLie X ∨ SporadicList X := by
  unfold SQTKSimpleList AltList OddList SQTKCharTwoLie SporadicList IsSQTKSporadicName
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | (h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem sqtkSimpleList_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SQTKSimpleList Y) : SQTKSimpleList X := by
  rw [sqtkSimpleList_iff] at h ⊢
  rcases h with h | h | h | h
  · obtain ⟨n, h5, h8, ⟨e'⟩⟩ := h
    exact Or.inl ⟨n, h5, h8, ⟨e.trans e'⟩⟩
  · obtain ⟨p, hp, hp2, h⟩ := h
    refine Or.inr (Or.inl ⟨p, hp, hp2, ?_⟩)
    rcases h with ⟨f, hf, h⟩ | h | h
    · exact Or.inl ⟨f, hf, statedClassicalModel_of_mulEquiv e h⟩
    · exact Or.inr (Or.inl (statedClassicalModel_of_mulEquiv e h))
    · exact Or.inr (Or.inr (statedClassicalModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (SQTKCharTwoLie.of_mulEquiv e h)))
  · obtain ⟨s, hs, ⟨e'⟩⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨s, hs, ⟨e.trans e'⟩⟩))

theorem sqtkSimpleList_component
    {G : Type} [Group G] [Finite G] (hloc : LocalSQTK G)
    {H : Subgroup G} (hH : CFSG.Open.pCoreOf 2 H ≠ ⊥) {L : Subgroup G} (hL : IsComponentIn L H) :
    SQTKSimpleList (↥L ⧸ Subgroup.center ↥L) := by
  have hq : CFSG.IsQuasisimple (L.subgroupOf H) := hL.2.1
  have : IsSimpleGroup ((L.subgroupOf H) ⧸ Subgroup.center (L.subgroupOf H)) := hq.2.1
  have hlist := cl_lit_sqtk_simple_list_section H (hloc H hH) (L.subgroupOf H)
    (Subgroup.center (L.subgroupOf H)) hq.2.2
  let e₀ : (L.subgroupOf H) ≃* L := Subgroup.subgroupOfEquivOfLe hL.1
  let e : (↥L ⧸ Subgroup.center ↥L) ≃*
      ((L.subgroupOf H) ⧸ Subgroup.center (L.subgroupOf H)) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center (L.subgroupOf H)) e₀.symm
      (Subgroup.map_center_eq e₀.symm)
  exact sqtkSimpleList_of_mulEquiv e hlist

end CFSG.QuasithinUnique.Ch1
