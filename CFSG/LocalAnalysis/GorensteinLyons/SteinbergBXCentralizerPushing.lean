module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_map_subtype_iff)

variable {G : Type} [Group G]

theorem mem_normalizer_map_of_characteristic [Finite G] {R : Subgroup G} (D : Subgroup R)
    [hD : D.Characteristic] {g : G} (hg : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer ((D.map R.subtype : Subgroup G) : Set G) := by
  have hR : R.map (MulAut.conj g).toMonoidHom = R := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact (mem_normalizer_iff.mp hg r).mp hr
    · intro r hr
      refine ⟨g⁻¹ * r * g, ?_, by simp [mul_assoc]⟩
      simpa using (mem_normalizer_iff.mp (inv_mem hg) r).mp hr
  let ψ : MulAut R := ((MulAut.conj g).subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  have hψ : ∀ r : R, ((ψ r : R) : G) = g * r * g⁻¹ := fun _ => rfl
  have hDψ := characteristic_iff_map_eq.mp hD ψ
  apply mem_normalizer_fintype
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨ψ d, ?_, hψ d⟩
  rw [← hDψ]
  exact mem_map_of_mem _ hd

theorem map_subtype_pCore_map (p : ℕ) (H : Subgroup G) (S : Subgroup H) :
    ((CFSG.pCore p S).map S.subtype).map H.subtype =
      (CFSG.pCore p (S.map H.subtype)).map (S.map H.subtype).subtype := by
  let e := S.equivMapOfInjective H.subtype H.subtype_injective
  have he := CFSG.pCore_map_iso p e
  have hcomp : H.subtype.comp S.subtype = (S.map H.subtype).subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [map_map, hcomp, ← map_map, he]

theorem map_subtype_iSup_conjugate (H A R : Subgroup G) (hAH : A ≤ H) (hRH : R ≤ H) :
    (⨆ m ∈ A.subgroupOf H, CFSG.conjugate (R.subgroupOf H) m).map H.subtype =
      ⨆ a ∈ A, CFSG.conjugate R a := by
  have hconj : ∀ m : H, (CFSG.conjugate (R.subgroupOf H) m).map H.subtype =
      CFSG.conjugate R (m : G) := by
    intro m
    rw [CFSG.conjugate, CFSG.conjugate, map_map]
    have hcomp : H.subtype.comp (MulAut.conj m⁻¹).toMonoidHom =
        (MulAut.conj (m : G)⁻¹).toMonoidHom.comp H.subtype := by
      ext x
      rfl
    rw [hcomp, ← map_map, subgroupOf_map_subtype, inf_of_le_left hRH]
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun m => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hm => ?_
    rw [hconj]
    exact le_iSup₂_of_le (m : G) (mem_subgroupOf.mp hm) le_rfl
  · refine iSup₂_le fun a ha => ?_
    refine le_iSup_of_le ⟨a, hAH ha⟩ ?_
    rw [Subgroup.map_iSup]
    refine le_iSup_of_le (mem_subgroupOf.mpr ha) ?_
    rw [hconj]

variable [Finite G]

end CFSG.LocalAnalysis.GorensteinLyons
