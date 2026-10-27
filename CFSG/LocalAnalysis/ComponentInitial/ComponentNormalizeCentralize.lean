module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

theorem map_conj_centralizer (U : Subgroup G) (g : G) :
    (centralizer (U : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ((U.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  simp only [mem_map, mem_centralizer_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [show g * u * g⁻¹ * (g * y * g⁻¹) = g * (u * y) * g⁻¹ by group, hy u hu]
    group
  · intro hx
    refine ⟨g⁻¹ * x * g, fun u hu => ?_, by group⟩
    have := hx (g * u * g⁻¹) ⟨u, hu, rfl⟩
    calc u * (g⁻¹ * x * g) = g⁻¹ * (g * u * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * u * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * u := by group

theorem map_conj_eq_of_isComponentOf_centralizer [Finite G] {A U : Subgroup G}
    (hA : CFSG.Assembly.IsComponentOf A (centralizer (U : Set G))) (hZ : center A = ⊥) {g : G}
    (hgU : U.map (MulAut.conj g).toMonoidHom = U) {e : G} (he : e ∈ A) (he1 : e ≠ 1)
    (hge : g * e * g⁻¹ = e) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  have hA' := isComponentOf_map_conj hA g
  rw [map_conj_centralizer, hgU] at hA'
  rcases isComponentOf_eq_or_commute hA' hA with h | h
  · exact h
  · exfalso
    have he' : e ∈ A.map (MulAut.conj g).toMonoidHom :=
      ⟨e, he, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hge]⟩
    have hle := (commutator_eq_bot_iff_le_centralizer).1 h
    have hcen : (⟨e, he⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      rintro ⟨z, hz⟩
      exact Subtype.ext ((mem_centralizer_iff.1 (hle he')) z hz)
    rw [hZ, mem_bot] at hcen
    exact he1 (congrArg Subtype.val hcen)

theorem le_centralizer_of_le_normalizer {A N Y : Subgroup G} [IsSimpleGroup Y]
    (hYA : Y ≤ normalizer (A : Set G)) (hNY : N ≤ Y) (hNA : N ≤ centralizer (A : Set G))
    (hN : N ≠ ⊥) :
    Y ≤ centralizer (A : Set G) := by
  set C := (centralizer (A : Set G)).subgroupOf Y
  have hCn : C.Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [mem_subgroupOf, mem_centralizer_iff] at hx ⊢
    intro a ha
    have hya : (y : G)⁻¹ * a * (y : G)⁻¹⁻¹ ∈ A :=
      (mem_normalizer_iff.1 (hYA (inv_mem y.2)) a).1 ha
    have hxa := hx _ hya
    simp only [inv_inv] at hxa
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc a * (y * x * (y : G)⁻¹) = y * ((y : G)⁻¹ * a * y * x) * (y : G)⁻¹ := by group
      _ = y * (x * ((y : G)⁻¹ * a * y)) * (y : G)⁻¹ := by rw [hxa]
      _ = y * x * (y : G)⁻¹ * a := by group
  rcases Subgroup.Normal.eq_bot_or_eq_top C with h | h
  · exfalso
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNY hn⟩ : Y) ∈ C := by rw [mem_subgroupOf]; exact hNA hn
    rw [h, mem_bot] at this
    exact (mem_bot).2 (congrArg Subtype.val this)
  · intro y hy
    have : (⟨y, hy⟩ : Y) ∈ C := by rw [h]; exact mem_top _
    exact this

end CFSG.LocalAnalysis.ComponentInitial
