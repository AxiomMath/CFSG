module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.GroupTheory

variable {Y Y' : Type} [Group Y] [Group Y']

theorem IsGomiL2.of_mulEquiv (e : Y ≃* Y') (h : IsGomiL2 Y) : IsGomiL2 Y' :=
  h.imp (fun ⟨f⟩ => ⟨e.symm.trans f⟩) fun ⟨d, hd, ⟨f⟩⟩ => ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem IsGomiU3.of_mulEquiv (e : Y ≃* Y') (h : IsGomiU3 Y) : IsGomiU3 Y' :=
  let ⟨d, hd, ⟨f⟩⟩ := h; ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem IsGomiSz.of_mulEquiv (e : Y ≃* Y') (h : IsGomiSz Y) : IsGomiSz Y' :=
  let ⟨d, hd, ⟨f⟩⟩ := h; ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem IsGomiL3.of_mulEquiv (e : Y ≃* Y') (h : IsGomiL3 Y) : IsGomiL3 Y' :=
  let ⟨d, hd, ⟨f⟩⟩ := h; ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem IsGomiSp4.of_mulEquiv (e : Y ≃* Y') (h : IsGomiSp4 Y) : IsGomiSp4 Y' :=
  h.imp (fun ⟨f⟩ => ⟨e.symm.trans f⟩) fun ⟨d, hd, ⟨f⟩⟩ => ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem IsGomiChevTwo.of_mulEquiv (e : Y ≃* Y') (h : IsGomiChevTwo Y) : IsGomiChevTwo Y' := by
  obtain ⟨hQ, hp, hChev⟩ := h
  refine ⟨hQ.of_mulEquiv e.symm, ?_, ?_⟩
  · rw [← CFSG.pCore_map_iso 2 e, hp, Subgroup.map_bot]
  · have eZ := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y') e
      (Subgroup.map_center_eq e)
    rcases hChev with ⟨d, hd, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨d, hd, ⟨φ⟩⟩
    · exact Or.inl ⟨d, hd, ⟨eZ.symm.trans φ⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨eZ.symm.trans φ⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hd, ⟨eZ.symm.trans φ⟩⟩)

private theorem map_subtype_inf_normalizer_gcm {G : Type} [Group G] {H : Subgroup G}
    (R L : Subgroup H) :
    (L.map H.subtype) ⊓ Subgroup.normalizer ((R.map H.subtype : Subgroup G) : Set G) =
      (L ⊓ Subgroup.normalizer (R : Set H)).map H.subtype := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨hyL, hyN⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hyL
    refine Subgroup.mem_map_of_mem H.subtype ⟨hl, ?_⟩
    have h2 := Subgroup.le_normalizer_comap H.subtype hyN
    rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h2
  · rw [Subgroup.map_inf L (Subgroup.normalizer (R : Set H)) H.subtype H.subtype_injective]
    exact inf_le_inf_left _ (Subgroup.le_normalizer_map (H := R) H.subtype)

theorem IsGomiParabolicSwap.map_subtype {G : Type} [Group G] {H : Subgroup G} {S L : Subgroup H}
    (h : IsGomiParabolicSwap S L) : IsGomiParabolicSwap (S.map H.subtype) (L.map H.subtype) := by
  obtain ⟨s, hs, P, hP1, hP2, hsP⟩ := h
  refine ⟨H.subtype s, ⟨Subgroup.mem_map_of_mem H.subtype hs.1, ?_⟩,
    P.map H.subtype, ?_, ?_, ?_⟩
  · exact Subgroup.le_normalizer_map (H := L) H.subtype (Subgroup.mem_map_of_mem H.subtype hs.2)
  · rw [← Subgroup.map_inf S L H.subtype H.subtype_injective,
      map_subtype_inf_normalizer_gcm (S ⊓ L) L]
    exact (Subgroup.map_lt_map_iff_of_injective (f := H.subtype) H.subtype_injective).mpr hP1
  · exact (Subgroup.map_lt_map_iff_of_injective (f := H.subtype) H.subtype_injective).mpr hP2
  · intro hsP'
    apply hsP
    have h2 := Subgroup.le_normalizer_comap H.subtype hsP'
    rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h2

theorem IsGomiThreeCycle.map_subtype {G : Type} [Group G] {H : Subgroup G} {n : ℕ}
    {K : Subgroup H} {x : H} (h : IsGomiThreeCycle n K x) :
    IsGomiThreeCycle n (K.map H.subtype) (x : G) := by
  obtain ⟨hx, φ, hφ⟩ := h
  refine ⟨Subgroup.mem_map_of_mem H.subtype hx,
    (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).symm.trans φ, ?_⟩
  have hsymm : (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).symm
      ⟨(x : G), Subgroup.mem_map_of_mem H.subtype hx⟩ = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact congrArg Subtype.val
      (Equiv.Set.image_symm_apply H.subtype K H.subtype_injective x
        (Subgroup.mem_map_of_mem H.subtype hx))
  simpa only [MulEquiv.trans_apply, hsymm] using hφ

end CFSG.GroupTheory
