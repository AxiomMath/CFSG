module

public import CFSG.Dihedral.BlueprintDefs
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint

variable {G H : Type} [Group G] [Group H]

theorem fullAutomorphismImage_of_map_equiv (e : G ≃* H) (A V : Subgroup G)
    (h : FullAutomorphismImage (A.map e.toMonoidHom) (V.map e.toMonoidHom)) :
    FullAutomorphismImage A V := by
  intro a
  let f : V ≃* V.map e.toMonoidHom := e.subgroupMap V
  let b : MulAut (V.map e.toMonoidHom) := f.symm.trans (a.trans f)
  obtain ⟨y, hyA, hy⟩ := h b
  obtain ⟨x, hxA, hxy⟩ := Subgroup.mem_map.mp hyA
  change e x = y at hxy
  refine ⟨x, hxA, ?_⟩
  intro v
  apply e.injective
  have h := hy (f v)
  change (f (a (f.symm (f v))) : H) = y * (f v : H) * y⁻¹ at h
  rw [f.symm_apply_apply] at h
  change e (a v : G) = y * e (v : G) * y⁻¹ at h
  simpa only [← hxy, map_mul, map_inv] using h

theorem cycles_of_map_equiv (e : G ≃* H) (A V : Subgroup G)
    (h : Cycles (A.map e.toMonoidHom) (V.map e.toMonoidHom)) : Cycles A V := by
  obtain ⟨y, hyA, hyN, hy⟩ := h
  obtain ⟨x, hxA, hxy⟩ := Subgroup.mem_map.mp hyA
  change e x = y at hxy
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective V e.bijective] at hyN
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyN
    have hzx : z = x := e.injective (hzy.trans hxy.symm)
    rwa [hzx] at hz
  refine ⟨x, hxA, hxN, ?_⟩
  intro v hv hvne heq
  apply hy (e v) (Subgroup.mem_map_of_mem e.toMonoidHom hv)
  · intro he
    exact hvne (e.injective (by simpa only [map_one] using he))
  · rw [← hxy]
    simpa only [map_mul, map_inv] using congrArg e heq

theorem fullAutomorphismImage_normalizer_inf_of_map_equiv (e : G ≃* H)
    (P V : Subgroup G)
    (h : FullAutomorphismImage (Subgroup.normalizer (P.map e.toMonoidHom : Set H) ⊓
      Subgroup.normalizer (V.map e.toMonoidHom : Set H)) (V.map e.toMonoidHom)) :
    FullAutomorphismImage (Subgroup.normalizer (P : Set G) ⊓
      Subgroup.normalizer (V : Set G)) V := by
  apply fullAutomorphismImage_of_map_equiv e
  rw [Subgroup.map_inf (f := e.toMonoidHom) (Subgroup.normalizer (P : Set G))
      (Subgroup.normalizer (V : Set G)) e.injective,
    Subgroup.map_normalizer_eq_of_bijective P e.bijective,
    Subgroup.map_normalizer_eq_of_bijective V e.bijective]
  exact h

theorem cycles_normalizer_of_map_equiv (e : G ≃* H) (P V : Subgroup G)
    (h : Cycles (Subgroup.normalizer (P.map e.toMonoidHom : Set H))
      (V.map e.toMonoidHom)) : Cycles (Subgroup.normalizer (P : Set G)) V := by
  apply cycles_of_map_equiv e
  rw [Subgroup.map_normalizer_eq_of_bijective P e.bijective]
  exact h

end CFSG.DihedralBlueprint
