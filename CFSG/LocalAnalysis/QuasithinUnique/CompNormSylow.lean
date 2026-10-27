module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.QuasithinUnique

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_sylow_eq_subgroupOf_of_normal (S : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ P : Sylow p N, (P : Subgroup N) = (S : Subgroup G).subgroupOf N := by
  obtain ⟨Q, hQ⟩ := (default : Sylow p N).exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hmem : ∀ x : G, x ∈ (Q : Subgroup G) ↔ g⁻¹ * x * g ∈ (S : Subgroup G) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hmap : (S : Subgroup G).subgroupOf N =
      ((Q : Subgroup G).subgroupOf N).map (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom := by
    ext x
    simp only [mem_subgroupOf, mem_map]
    constructor
    · intro hx
      refine ⟨MulAut.conjNormal (H := N) g x, ?_, ?_⟩
      · rw [MulAut.conjNormal_apply, hmem]
        simpa [mul_assoc] using hx
      · apply Subtype.ext
        simp
    · rintro ⟨y, hy, rfl⟩
      have := (hmem y).mp hy
      simpa [MulAut.conjNormal_apply] using this
  refine ⟨Sylow.ofCard ((S : Subgroup G).subgroupOf N) ?_, rfl⟩
  rw [hmap, Subgroup.card_map_of_injective
      (f := (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom)
      (MulAut.conjNormal (H := N) g⁻¹).injective,
    show ((Q : Subgroup G).subgroupOf N) = ((default : Sylow p N) : Subgroup N) from hQ]
  exact Sylow.card_eq_multiplicity _

theorem exists_sylow_map_eq_inf_of_normal (S : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ P : Sylow p N, (P : Subgroup N).map N.subtype = (S : Subgroup G) ⊓ N := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_subgroupOf_of_normal S N
  exact ⟨P, by rw [hP, Subgroup.subgroupOf_map_subtype]⟩

theorem exists_sylow_map_eq_inf_of_subnormal (S : Sylow p G) {H : Subgroup G}
    (hH : H.IsSubnormal) :
    ∃ P : Sylow p H, (P : Subgroup H).map H.subtype = (S : Subgroup G) ⊓ H := by
  induction hH with
  | top =>
    let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
    have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨S.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, inf_top_eq]
    convert Subgroup.map_id (S : Subgroup G)
    ext x
    rfl
  | step H K hHK hK hN ih =>
    obtain ⟨PK, hPK⟩ := ih
    obtain ⟨Q, hQ⟩ := exists_sylow_map_eq_inf_of_normal PK (H.subgroupOf K)
    let e : H.subgroupOf K ≃* H := Subgroup.subgroupOfEquivOfLe hHK
    have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨Q.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : H.subtype.comp e.toMonoidHom = K.subtype.comp (H.subgroupOf K).subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hQ, Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hPK,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHK, inf_assoc, inf_eq_right.mpr hHK]

end CFSG.QuasithinUnique
