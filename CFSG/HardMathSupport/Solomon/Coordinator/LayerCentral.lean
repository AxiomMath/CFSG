module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralAlg
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Ambient

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

theorem subgroupOf_map_eq_map_subgroupMap (φ : G →* G') {X J : Subgroup G} (hJX : J ≤ X) :
    (J.map φ).subgroupOf (X.map φ) = (J.subgroupOf X).map (φ.subgroupMap X) := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj, hjz⟩ := hz
    refine ⟨⟨j, hJX hj⟩, hj, ?_⟩
    exact Subtype.ext hjz
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem glaPComponent_map_central {p : ℕ} (hp : p.Prime) (φ : G →* G') {X : Subgroup G}
    (hc : ∀ y ∈ X ⊓ φ.ker, ∀ x ∈ X, x * y = y * x) {J : Subgroup G}
    (hJ : GLAPComponent p X J) : GLAPComponent p (X.map φ) (J.map φ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hJ' := (i183_glaPComponent_iff_isPComponent hp).1 hJ
  have hker : (φ.subgroupMap X).ker ≤ Subgroup.center ↥X := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hx1 : (x : G) ∈ φ.ker := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact Subtype.ext (hc _ ⟨x.2, hx1⟩ (g : G) g.2)
  have := isPComponent_map_central p (φ.subgroupMap X) (MonoidHom.subgroupMap_surjective φ X)
    hker hJ'.2
  refine (i183_glaPComponent_iff_isPComponent hp).2 ⟨Subgroup.map_mono hJ'.1, ?_⟩
  rw [subgroupOf_map_eq_map_subgroupMap φ hJ'.1]
  exact this

theorem exists_glaPComponent_map_central {p : ℕ} (hp : p.Prime) (φ : G →* G') {X : Subgroup G}
    (hc : ∀ y ∈ X ⊓ φ.ker, ∀ x ∈ X, x * y = y * x) {J' : Subgroup G'}
    (hJ' : GLAPComponent p (X.map φ) J') :
    ∃ J : Subgroup G, GLAPComponent p X J ∧ J.map φ = J' := by
  have : Fact p.Prime := ⟨hp⟩
  have hker : (φ.subgroupMap X).ker ≤ Subgroup.center ↥X := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hx1 : (x : G) ∈ φ.ker := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact Subtype.ext (hc _ ⟨x.2, hx1⟩ (g : G) g.2)
  obtain ⟨hJ'le, hJ'pc⟩ := (i183_glaPComponent_iff_isPComponent hp).1 hJ'
  obtain ⟨Ĵ, hĴ, hĴmap⟩ := exists_isPComponent_map_central p (φ.subgroupMap X)
    (MonoidHom.subgroupMap_surjective φ X) hker hJ'pc
  refine ⟨Ĵ.map X.subtype, ?_, ?_⟩
  · refine (i183_glaPComponent_iff_isPComponent hp).2 ⟨Subgroup.map_subtype_le _, ?_⟩
    have h : (Ĵ.map X.subtype).subgroupOf X = Ĵ :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective Ĵ
    rw [h]
    exact hĴ
  · rw [Subgroup.map_map]
    have h2 : (X.map φ).subtype.comp (φ.subgroupMap X) = φ.comp X.subtype := by ext x; rfl
    rw [← h2, ← Subgroup.map_map, hĴmap, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hJ'le

end Ambient

end CFSG.HardMathSupport.Solomon.Coordinator
