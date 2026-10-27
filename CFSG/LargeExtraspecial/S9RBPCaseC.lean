module

public import CFSG.LargeExtraspecial.S9RBPCaseB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

namespace TriHyp

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} {τ₁ τ₂ : S.O} (T : TriHyp H C ht ht1 hVQ τ₁ τ₂)
include T

theorem sub_mem_Fix {g' : G} (H' : Hyp4 S g') (C' : Cons311 S g')
    (hc : S.cl (g' * S.z * g'⁻¹) ∈ Vt S g t) (hLR : S.Lbar g' ≤ Rbar S g t) {x : S.Qt}
    (hx : x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) {l : S.O}
    (hl : l ∈ S.Lbar g') :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈
      (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓ fixMod S (S.Lbar g') (Vt S g t) := by
  refine ⟨sub_mem (T.apply_mem_U (hLR hl) hx) hx, fun l' hl' => ?_⟩
  have hP := apply_sub_mem_clSub_of_mem_Wt C' hc H'.conj_mem (T.U_le_Wt hx) hl
  have hspan : (ZMod 2) ∙ S.cl (g' * S.z * g'⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hc
  exact hspan (Lbar_apply_sub_mem_span' H'.conj_mem hP hl')

theorem gen (hNo : NoA2 S g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {w₂ : S.Qt} (hw₂ : w₂ ∈ Wt S g t)
    (h0 : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ≠ 0)
    (hf : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ∈ fixMod S (S.Lbar ((h : G) * g)) (Vt S g t))
    {k : S.O} (hk : k ∈ Rbar S g t)
    (hkT : ∀ x ∈ (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
      fixMod S (S.Lbar g) (Vt S g t), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t)
    (hku : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) -
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) ∈ Vt S g t) :
    ∀ x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := by
  have hth := mem_Lbar_of_pair H ht hh
  obtain ⟨d₂, l₂⟩ := T.plane (Lbar_mul_le_Rbar hth) hw₂ h0 hf
  have hab := T.Fix_inf_Fix_le hNo hh hb
  have dTa := T.finrank_Fix hNo
  have dU := T.finrank_U
  set U := Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  set Ta := U ⊓ fixMod S (S.Lbar g) (Vt S g t) with hTa
  set P₂ := Vt S g t ⊔ (ZMod 2) ∙ ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) ⊔
    (ZMod 2) ∙ ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) with hP₂
  have hP₂a : Ta ⊓ P₂ ≤ Vt S g t := le_trans (inf_le_inf_left _ l₂) hab
  have e1 := Submodule.finrank_mono hP₂a
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq Ta P₂
  have hsup : Ta ⊔ P₂ = U :=
    Submodule.eq_of_le_of_finrank_le (sup_le inf_le_left (l₂.trans inf_le_left)) (by omega)
  set F := (Vt S g t).comap ((k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id) with hF
  have hmemF : ∀ x, x ∈ F ↔ (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := fun x => by
    simp [hF]
  have hVF : Vt S g t ≤ F := fun x hx =>
    (hmemF x).mpr (sub_mem (apply_mem_Vt_of_mem_Rbar H.conj_mem hk hx) hx)
  have hy := T.transfer hk hw₂ hku
  have hle : Ta ⊔ P₂ ≤ F := by
    refine sup_le (fun x hx => (hmemF x).mpr (hkT x hx)) (sup_le (sup_le hVF ?_) ?_)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr ((hmemF _).mpr hku)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr ((hmemF _).mpr hy)
  intro x hx
  rw [← hsup] at hx
  exact (hmemF x).mp (hle hx)

end TriHyp

end CFSG.LargeExtraspecial.S9.RB
