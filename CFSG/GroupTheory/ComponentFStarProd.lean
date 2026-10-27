module

public import CFSG.Adapters.GeneralizedFitting
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X A B : Type} [Group X] [Finite X] [Group A] [Group B] [IsSimpleGroup A]

theorem component_le_genFittingFStar {C : Subgroup X} (hC : CFSG.IsComponent C) :
    C ≤ CFSG.Open.genFittingFStar X := by
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, CFSG.generalizedFitting.eq_sup]
  exact (CFSG.LocalCores.component_le_layer hC).trans le_sup_right

private theorem image_component_map_eq_range_inl (hB : ∀ a b : B, a * b = b * a)
    (φ : ↥(CFSG.Open.genFittingFStar X) ≃* A × B) {C : Subgroup X}
    (hC : CFSG.IsComponent C) :
    (C.subgroupOf (CFSG.Open.genFittingFStar X)).map φ.toMonoidHom =
      (MonoidHom.inl A B).range := by
  have hD : CFSG.IsComponent (C.subgroupOf (CFSG.Open.genFittingFStar X)) :=
    CFSG.LocalCores.component_overgroup hC (component_le_genFittingFStar hC)
  have hE : CFSG.IsComponent
      ((C.subgroupOf (CFSG.Open.genFittingFStar X)).map φ.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv φ hD
  set E : Subgroup (A × B) :=
    (C.subgroupOf (CFSG.Open.genFittingFStar X)).map φ.toMonoidHom with hEdef
  have hEk : E ≤ (MonoidHom.inl A B).range := by
    have hker : E ≤ (MonoidHom.snd A B).ker := by
      rw [← Subgroup.map_eq_bot_iff, ← Subgroup.isPerfect_iff.mp hE.1.1,
        Subgroup.map_commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hB y x
    intro x hx
    have hx2 : x.2 = 1 := by
      have := (MonoidHom.mem_ker).mp (hker hx)
      simpa using this
    refine ⟨x.1, ?_⟩
    cases x with
    | mk a b => exact Prod.ext rfl hx2.symm
  have hne : E ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot E).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hE.1)
  have hcomapne : E.comap (MonoidHom.inl A B) ≠ ⊥ := by
    intro hbot
    haveI : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hE.1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥E)
    have hx1 : (x : A × B) ≠ 1 := fun h => hx (Subtype.ext h)
    have hxE : (x : A × B) ∈ E := x.2
    obtain ⟨a, ha⟩ := hEk hxE
    have haE : a ∈ E.comap (MonoidHom.inl A B) := by
      rw [Subgroup.mem_comap]
      rw [ha]
      exact hxE
    rw [hbot, Subgroup.mem_bot] at haE
    exact hx1 (by rw [← ha, haE]; rfl)
  have hsub : (E.comap (MonoidHom.inl A B)).IsSubnormal :=
    Subgroup.IsSubnormal.comap (MonoidHom.inl A B) hE.2
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
    (inferInstance : IsSimpleGroup A) hsub with h | h
  · exact absurd h hcomapne
  · refine le_antisymm hEk fun x hx => ?_
    obtain ⟨a, rfl⟩ := hx
    have ha : a ∈ E.comap (MonoidHom.inl A B) := h ▸ Subgroup.mem_top a
    exact ha

theorem eq_of_isComponent_of_mulEquiv_prod (hB : ∀ a b : B, a * b = b * a)
    (φ : ↥(CFSG.Open.genFittingFStar X) ≃* A × B) {C₁ C₂ : Subgroup X}
    (h₁ : CFSG.IsComponent C₁) (h₂ : CFSG.IsComponent C₂) : C₁ = C₂ := by
  have hD12 : C₁.subgroupOf (CFSG.Open.genFittingFStar X) =
      C₂.subgroupOf (CFSG.Open.genFittingFStar X) := by
    apply Subgroup.map_injective (f := φ.toMonoidHom)
    · exact φ.injective
    · rw [image_component_map_eq_range_inl hB φ h₁,
        image_component_map_eq_range_inl hB φ h₂]
  have hD12' : C₁ ⊓ CFSG.Open.genFittingFStar X =
      C₂ ⊓ CFSG.Open.genFittingFStar X := Subgroup.subgroupOf_inj.mp hD12
  rwa [inf_of_le_left (component_le_genFittingFStar h₁),
    inf_of_le_left (component_le_genFittingFStar h₂)] at hD12'

end CFSG.GroupTheory
