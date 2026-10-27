module

public import CFSG.LargeExtraspecial.S9RBPTriA
public import CFSG.LargeExtraspecial.S9RBPa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem fixMod_map {X : Subgroup S.O} {V : Submodule (ZMod 2) S.Qt} {r : S.O}
    (hV : V.map (r : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap = V) :
    (fixMod S X V).map (r : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap =
      fixMod S (X.map (MulAut.conj r).toMonoidHom) V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearEquiv.coe_coe]
    rw [coe_mul_apply, coe_mul_apply, inv_apply_apply_O, ← map_sub, ← hV]
    exact Submodule.mem_map_of_mem (hy l hl)
  · intro hx
    refine ⟨((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x, fun l hl => ?_, by
      simp only [LinearEquiv.coe_coe, apply_inv_apply_O]⟩
    have h1 := hx (r * l * r⁻¹) ⟨l, hl, rfl⟩
    rw [← hV] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
        ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = y := by
      have := congrArg ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) hyx
      simp only [LinearEquiv.coe_coe, inv_apply_apply_O] at this
      rw [this, map_sub, coe_mul_apply, coe_mul_apply, inv_apply_apply_O]
    rw [e]
    exact hy

theorem map_eq_of_forall {X : Submodule (ZMod 2) S.Qt} {r : S.O}
    (h1 : ∀ x ∈ X, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ X)
    (h2 : ∀ x ∈ X, ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ X) :
    X.map (r : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap = X := by
  refine le_antisymm ?_ fun x hx => ⟨_, h2 x hx, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · simp only [LinearEquiv.coe_coe, apply_inv_apply_O]

namespace TriHyp

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} {τ₁ τ₂ : S.O} (T : TriHyp H C ht ht1 hVQ τ₁ τ₂)
include T

theorem exists_mem_clSub {g' : G} (H' : Hyp4 S g') (C' : Cons311 S g')
    (hc : S.cl (g' * S.z * g'⁻¹) ∈ Vt S g t) :
    ∃ w ∈ Wt S g t, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ 0 ∧
      (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ fixMod S (S.Lbar g') (Vt S g t) := by
  have f₁ := T.h₁.finrank_commSpace H C ht ht1 hVQ
  rw [T.data.finrank_eq] at f₁
  have k₁ := two_le_finrank_commSpace_inf_clSub H' C' (T.h₁.mem_Mbar ht) (T.fix₁ _ hc) f₁
  have hne : commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ S.clSub (S.QG ⊓ S.Qa g') ≠ ⊥ :=
    fun h0 => by rw [h0, finrank_bot] at k₁; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hw, rfl⟩ := exists_apply_sub_eq_of_mem T.inf₁ hu.1
  refine ⟨w, hw, hu0, fun l hl => ?_⟩
  have hspan : (ZMod 2) ∙ S.cl (g' * S.z * g'⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hc
  exact hspan (Lbar_apply_sub_mem_span' H'.conj_mem hu.2 hl)

theorem map_Fix {r : S.M} (hr : S.ρ r ∈ Rbar S g t) (g' : G) :
    ((Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
        fixMod S (S.Lbar g') (Vt S g t)).map ((S.ρ r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap =
      (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
        fixMod S (S.Lbar ((r : G) * g')) (Vt S g t) := by
  have haQ := H.conj_mem
  have hV : (Vt S g t).map ((S.ρ r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap = Vt S g t :=
    map_eq_of_forall (fun x hx => apply_mem_Vt_of_mem_Rbar haQ hr hx)
      (fun x hx => apply_mem_Vt_of_mem_Rbar haQ (inv_mem hr) hx)
  have hU : (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
      ((S.ρ r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap =
      Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    map_eq_of_forall (fun x hx => T.apply_mem_U hr hx) (fun x hx => T.apply_mem_U (inv_mem hr) hx)
  rw [Submodule.map_inf _ (LinearEquiv.injective _), hU, fixMod_map hV, Lbar_mul S r g']

theorem Fix_inf_Fix_le (hNo : NoA2 S g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    ((Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓ fixMod S (S.Lbar g) (Vt S g t)) ⊓
      ((Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
        fixMod S (S.Lbar ((h : G) * g)) (Vt S g t)) ≤ Vt S g t := by
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ T.data.tau_not_mem
  have hPI := pairInt_of_radBound H C ht ht1 hVQ hR
  have hCab := sup_Vt_inf_sup_Vt H C ht ht1 hVQ hh hb
    (clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR)
  intro x hx
  have hxW : x ∈ Wt S g t := T.U_le_Wt hx.1.1
  have ha := (forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hxW).mp hx.1.2
  have hb' := (forall_apply_sub_mem_Vt_iff_b H hNo C ht ht1 hVQ hh hb hPI hxW).mp hx.2.2
  rw [← hCab]
  exact ⟨ha, hb'⟩

theorem finrank_Fix (hNo : NoA2 S g) :
    finrank (ZMod 2) ↥((Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
      fixMod S (S.Lbar g) (Vt S g t)) = finrank (ZMod 2) (Vt S g t) + 2 := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  obtain ⟨w₁, hw₁, h0₁, hf₁⟩ := T.exists_mem_clSub H C (cl_a_mem_Vt ht)
  obtain ⟨w₂, hw₂, h0₂, hf₂⟩ := T.exists_mem_clSub (H.mul h) (C.mul h) (cl_mem_Vt hth)
  obtain ⟨d₁, l₁⟩ := T.plane (Lbar_le_Rbar ht) hw₁ h0₁ hf₁
  obtain ⟨d₂, l₂⟩ := T.plane (Lbar_mul_le_Rbar hth) hw₂ h0₂ hf₂
  have hab := T.Fix_inf_Fix_le hNo hh hb
  set Fa := (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
    fixMod S (S.Lbar g) (Vt S g t) with hFa
  set Fb := (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
    fixMod S (S.Lbar ((h : G) * g)) (Vt S g t) with hFb
  have e1 := Submodule.finrank_mono hab
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq Fa Fb
  have e3 := Submodule.finrank_mono (sup_le inf_le_left inf_le_left : Fa ⊔ Fb ≤
    Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have e4 := T.finrank_U
  have e5 := Submodule.finrank_mono l₁
  have e6 := Submodule.finrank_mono l₂
  omega

end TriHyp

end CFSG.LargeExtraspecial.S9.RB
