module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
public import CFSG.GroupTheory.SubgroupOfQuotientMap
import CFSG.GroupTheory.SubgroupOfQuotientMapCentral

public section

namespace CFSG.GroupTheory

open Subgroup

theorem isGomiAtom_map_subgroupOf_iff {G Γ : Type} [Group G] [Group Γ] {X D L U A : Subgroup G}
    {ψ : ↥X →* Γ} (hker : ψ.ker = D.subgroupOf X) (hLX : L ≤ X) (hAX : A ≤ X)
    (hDB : D ≤ L ⊓ normalizer (U : Set G)) (hDA : D ≤ A)
    (hB : (L.subgroupOf X).map ψ ⊓ normalizer (((U.subgroupOf X).map ψ : Subgroup Γ) : Set Γ) =
      ((L ⊓ normalizer (U : Set G)).subgroupOf X).map ψ) :
    IsGomiAtom ((L.subgroupOf X).map ψ) ((U.subgroupOf X).map ψ) ((A.subgroupOf X).map ψ) ↔
      IsGomiAtom L U A := by
  have hBX : L ⊓ normalizer (U : Set G) ≤ X := inf_le_left.trans hLX
  constructor
  · intro h
    rw [IsGomiAtom] at h
    rw [hB] at h
    refine ⟨?_, ?_, ?_⟩
    · exact (map_subgroupOf_lt_map_subgroupOf_iff hker hBX hAX hDB hDA).mp h.1
    · exact (map_subgroupOf_le_map_subgroupOf_iff hker hAX (hDB.trans inf_le_left)).mp h.2.1
    · intro Q hBQ hQA
      have hDQ : D ≤ Q := hDB.trans hBQ.le
      exact (map_subgroupOf_inj hker (hQA.trans hAX) hAX hDQ hDA).mp
        (h.2.2 _ ((map_subgroupOf_lt_map_subgroupOf_iff hker hBX (hQA.trans hAX) hDB hDQ).mpr hBQ)
          ((map_subgroupOf_le_map_subgroupOf_iff hker (hQA.trans hAX) hDA).mpr hQA))
  · intro h
    rw [IsGomiAtom] at h ⊢
    rw [hB]
    refine ⟨?_, ?_, ?_⟩
    · exact (map_subgroupOf_lt_map_subgroupOf_iff hker hBX hAX hDB hDA).mpr h.1
    · exact (map_subgroupOf_le_map_subgroupOf_iff hker hAX (hDB.trans inf_le_left)).mpr h.2.1
    · intro Q' hBQ' hQ'A
      let Q : Subgroup G := (Q'.comap ψ).map X.subtype
      have hDQ : D ≤ Q := by
        intro d hd
        have hk : ψ ⟨d, hLX (hDB hd).1⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hker]
          exact Subgroup.mem_subgroupOf.mpr hd
        exact Subgroup.mem_map.mpr ⟨⟨d, hLX (hDB hd).1⟩,
          by rw [Subgroup.mem_comap, hk]; exact Q'.one_mem, rfl⟩
      have hsub : Q.subgroupOf X = Q'.comap ψ := by
        change Q.comap X.subtype = Q'.comap ψ
        rw [show Q = (Q'.comap ψ).map X.subtype from rfl]
        exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
      have hQbar : (Q.subgroupOf X).map ψ = Q' := by
        rw [hsub, Subgroup.map_comap_eq_self
          (hQ'A.trans (Subgroup.map_le_range ψ (A.subgroupOf X)))]
      have hBQ : L ⊓ normalizer (U : Set G) < Q :=
        (map_subgroupOf_lt_map_subgroupOf_iff hker hBX (Subgroup.map_subtype_le _) hDB hDQ).mp
          (by rw [hQbar]; exact hBQ')
      have hQA : Q ≤ A :=
        (map_subgroupOf_le_map_subgroupOf_iff hker (Subgroup.map_subtype_le _) hDA).mp
          (by rw [hQbar]; exact hQ'A)
      rw [← hQbar, h.2.2 Q hBQ hQA]

end CFSG.GroupTheory
