module

public import CFSG.Quasithin.Background.C1PackImage

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

theorem barImage_map_conj {G : Type} [Group G] [Finite G] (H K : Subgroup G) (hK : K ≤ H)
    {g : G} (hg : g ∈ H) :
    C1Pack.barImage H (K.map (MulAut.conj g).toMonoidHom) =
      (C1Pack.barImage H K).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hg⟩)).toMonoidHom := by
  have hKsub : (K.map (MulAut.conj g).toMonoidHom).subgroupOf H =
      (K.subgroupOf H).map (MulAut.conj (⟨g, hg⟩ : ↥H)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hyK : (y : G) ∈ K.map (MulAut.conj g).toMonoidHom := hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hyK
      refine Subgroup.mem_map.mpr ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
      apply Subtype.ext
      simpa [MulAut.conj_apply] using hky
    · intro hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨(k : G), hkK, ?_⟩)
      have h := congrArg Subtype.val hky
      simpa [MulAut.conj_apply] using h
  have hcomp : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp
        (MulAut.conj (⟨g, hg⟩ : ↥H)).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hg⟩)).toMonoidHom.comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    ext x
    simp [MonoidHom.comp_apply, MulAut.conj_apply, MonoidHom.map_mul, MonoidHom.map_inv]
  rw [C1Pack.barImage, C1Pack.barImage, hKsub, Subgroup.map_map, hcomp, ← Subgroup.map_map]

end CFSG.GroupTheory

end
