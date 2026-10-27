module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open

theorem isComponent_subgroupOf_of_isComponentOf' {S : Type*} [Group S] {C L : Subgroup S}
    (h : IsComponentOf L C) : CFSG.IsComponent (L.subgroupOf C) := by
  rw [CFSG.isComponent_iff_open]
  refine ⟨le_top, ?_, ?_⟩
  · have h1 := h.2.1.comap C.subtype
    rwa [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self (H := C)] at h1
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe h.1).symm h.2.2

theorem glaLayer_le_map_layer {S : Type*} [Group S] (C : Subgroup S) :
    GLALayer C ≤ (CFSG.layer ↥C).map C.subtype := by
  refine sSup_le fun L hL => ?_
  have hLC : L ≤ C := hL.1
  rw [← Subgroup.map_subgroupOf_eq_of_le hLC]
  refine Subgroup.map_mono ?_
  rw [CFSG.layer.eq_sSup]
  exact le_sSup (isComponent_subgroupOf_of_isComponentOf' hL)

theorem map_layer_le_layer_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map (e : A →* B) ≤ CFSG.layer B := by
  rw [CFSG.layer.eq_sSup, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hL' : CFSG.IsComponent L := hL
  have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e
    ((CFSG.isComponent_iff_open L).1 hL')
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h1
  rw [CFSG.layer.eq_sSup]
  exact le_sSup ((CFSG.isComponent_iff_open _).2 h1)

theorem perfectInLayer_of_fixEquiv {S₁ S₂ : Type*} [Group S₁] [Group S₂] {α : MulAut S₁}
    {φ : MulAut S₂} (e : ↥(fixSubgroup α) ≃* ↥(fixSubgroup φ)) (h : PerfectInLayer φ) :
    PerfectInLayer α := by
  intro P hPC hP
  set C₁ := fixSubgroup α with hC₁
  set C₂ := fixSubgroup φ with hC₂
  set P₁ : Subgroup ↥C₁ := P.subgroupOf C₁ with hP₁def
  have hPmap : P₁.map C₁.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPC
  have hP₁ : ⁅P₁, P₁⁆ = P₁ := by
    have h1 : (⁅P₁, P₁⁆).map C₁.subtype = P₁.map C₁.subtype := by
      rw [Subgroup.map_commutator, hPmap, hP]
    exact Subgroup.map_injective C₁.subtype_injective h1
  set P₂ : Subgroup ↥C₂ := P₁.map e.toMonoidHom with hP₂def
  have hP₂ : ⁅P₂, P₂⁆ = P₂ := by
    rw [hP₂def, ← Subgroup.map_commutator, hP₁]
  set P₂' : Subgroup S₂ := P₂.map C₂.subtype with hP₂'def
  have hP₂'C : P₂' ≤ C₂ := Subgroup.map_subtype_le _
  have hP₂'perf : ⁅P₂', P₂'⁆ = P₂' := by
    rw [hP₂'def, ← Subgroup.map_commutator, hP₂]
  have h2 := h P₂' hP₂'C hP₂'perf
  have h3 : P₂ ≤ CFSG.layer ↥C₂ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := glaLayer_le_map_layer C₂ (h2 ⟨x, hx, rfl⟩)
    rw [show y = x from Subtype.ext hyx] at hy
    exact hy
  have h4 : P₁ ≤ CFSG.layer ↥C₁ := by
    intro x hx
    have hx2 : e x ∈ CFSG.layer ↥C₂ := h3 ⟨x, hx, rfl⟩
    have := map_layer_le_layer_of_equiv e.symm ⟨e x, hx2, rfl⟩
    simpa using this
  intro p hp
  have hp1 : (⟨p, hPC hp⟩ : ↥C₁) ∈ P₁ := hp
  exact map_layer_le_glaLayer C₁ ⟨_, h4 hp1, rfl⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
