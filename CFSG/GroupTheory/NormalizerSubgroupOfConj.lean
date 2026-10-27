module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem subgroupOf_map_conj_eq_map_normalizerMonoidHom {G : Type*} [Group G] {I L : Subgroup G}
    {c : G} (hcI : c ∈ Subgroup.normalizer (I : Set G)) :
    (L.map (MulAut.conj c).toMonoidHom).subgroupOf I =
      (L.subgroupOf I).map (Subgroup.normalizerMonoidHom I ⟨c, hcI⟩).toMonoidHom := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hx
    have hxl : c * l * c⁻¹ = (x : G) := hlx
    have hcI' : c⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
      (Subgroup.normalizer (I : Set G)).inv_mem hcI
    have hlI : l ∈ I := by
      have hle : l = c⁻¹ * (x : G) * c := by rw [← hxl]; group
      rw [hle]
      exact (by
        simpa using (Subgroup.mem_normalizer_iff.mp hcI' (x : G)).mp x.2)
    refine Subgroup.mem_map.mpr ⟨⟨l, hlI⟩, hl, ?_⟩
    apply Subtype.ext
    change (((Subgroup.normalizerMonoidHom I ⟨c, hcI⟩) ⟨l, hlI⟩ : ↥I) : G) = (x : G)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hxl
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyc : ((Subgroup.normalizerMonoidHom I ⟨c, hcI⟩) y : ↥I) = x := hyx
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine Subgroup.mem_map.mpr ⟨(y : G), hy, ?_⟩
    change c * (y : G) * c⁻¹ = (x : G)
    have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe
      (H := I) ⟨c, hcI⟩ y
    rw [hyc] at hcoe
    simpa using hcoe.symm

end CFSG.GroupTheory
