module

public import CFSG.GH74.Uniqueness.SU.SU5Facts

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

theorem mem_W_of_centralizes_U : ∀ g : J2Syl, (∀ u : J2Syl, u ∈ U → g * u = u * g) → g ∈ W := by
  decide +kernel

end J2Syl

variable {G : Type*} [Group G]

theorem exists_config_of_isJ2Type {S : Subgroup G} (hS : IsJ2Type S) :
    ∃ (T : Subgroup G) (x : G), J2Emb S T x := by
  obtain ⟨e⟩ := hS
  let f : J2Syl →* G := S.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := S.subtype_injective.comp e.symm.injective
  refine ⟨J2Syl.W.map f, f J2Syl.x0, f, hf, ?_, rfl, rfl⟩
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    exact (e.symm m).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp [f]⟩

theorem J2Facts.of_isJ2Type {S : Subgroup G} (hS : IsJ2Type S) :
    ∃ (T : Subgroup G) (x z : G), J2Facts S T x z := by
  obtain ⟨T, x, h⟩ := exists_config_of_isJ2Type hS
  obtain ⟨z, hz⟩ := h.exists_zgen
  exact ⟨T, x, z, h.facts hz⟩

namespace J2Emb

variable {S T : Subgroup G} {x : G}

theorem centralizer_normal_four (h : J2Emb S T x) {U : Subgroup G} (hUS : U ≤ S)
    (hUn : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) (hUE : IsE 2 U) :
    S ⊓ centralizer (U : Set G) = T := by
  have hU := h.unique_normal_four U hUS hUn hUE
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  rw [hU, Zc_map hf, J2Syl.Zc_W]
  apply le_antisymm
  · rintro _ ⟨⟨m, rfl⟩, hc⟩
    refine Subgroup.mem_map.2 ⟨m, J2Syl.mem_W_of_centralizes_U m (fun u hu => ?_), rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hc (f u) (Subgroup.mem_map_of_mem f hu)
    exact hf (by rw [map_mul, map_mul]; exact h1.symm)
  · rintro _ ⟨m, hm, rfl⟩
    refine ⟨⟨m, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hmW : m ∈ J2Syl.W := hm
    have h2 := J2Syl.U_central u m hu hmW
    rw [← map_mul, ← map_mul, h2]

end J2Emb

end CFSG.GH74.Uniqueness.SU.SU5
