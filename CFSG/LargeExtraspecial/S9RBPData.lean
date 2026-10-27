module

public import CFSG.LargeExtraspecial.S9PA
public import CFSG.LargeExtraspecial.S9RBTriA
public import CFSG.LargeExtraspecial.S9RBType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

structure Step5Data (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) : Prop where
  finrank_eq : finrank (ZMod 2) (Vt S g t) = 4
  transitive : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v
  tau_not_mem : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t
  card_Abar : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 4 = 2 ^ (S.width - 1)

theorem step5Data_pgl25 (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hP : PGL25Case H C ht ht1 hVQ) :
    Step5Data H C ht ht1 hVQ :=
  ⟨hP.finrank_eq, hP.transitive, hP.tau_not_mem, card_Abar_mul_four_pgl25 H C ht ht1 hVQ hP⟩

namespace Step5Data

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} (D : Step5Data H C ht ht1 hVQ)
include D

theorem N0bar_apply {x : S.O} (hx : x ∈ N0bar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ D.tau_not_mem
  have hPab := clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR
  exact apply_sub_mem_Vt_of_mem_N0bar H
    (fun k hk w hw => apply_sub_mem_Vt_a H C ht ht1 hVQ hh hb hPab hk hw) hx hw

theorem apply_sub_mem_Vt_of_fix {x : S.O} (hxM : x ∈ S.Mbar) (hxt : x * t = t * x)
    (hfix : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {r : S.O}
    (hr : r ∈ Rbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Vt S g t := by
  have haQ := H.conj_mem
  have hD := dtEqConj_of_transitive H ht D.transitive
  have hxW : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t := by
    intro w hw
    have hW := (commSpace_t_eq H C ht ht1 hVQ).2
    rw [← hW, mem_fixSpace] at hw ⊢
    rw [← coe_mul_apply, ← hxt, coe_mul_apply, hw]
  let E : Subgroup S.O :=
    { carrier := {r | r ∈ Rbar S g t ∧ ∀ w ∈ Wt S g t,
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
          (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Vt S g t}
      mul_mem' := by
        rintro r s ⟨hr, hr'⟩ ⟨hs, hs'⟩
        refine ⟨mul_mem hr hs, fun w hw => ?_⟩
        have hsw := apply_mem_Wt H hs hw
        rw [coe_mul_apply, coe_mul_apply]
        have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) =
            ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
                ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) +
            (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
                ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
          rw [map_sub]; abel
        rw [e]
        exact add_mem (hr' _ hsw) (apply_mem_Vt_of_mem_Rbar haQ hr (hs' w hw))
      one_mem' := ⟨one_mem _, fun w _ => by
        rw [show ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w from rfl,
          show ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
            (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w from rfl, sub_self]
        exact zero_mem _⟩
      inv_mem' := by
        rintro r ⟨hr, hr'⟩
        refine ⟨inv_mem hr, fun w hw => ?_⟩
        have hw' := apply_mem_Wt H (inv_mem hr) hw
        have h1 := apply_mem_Vt_of_mem_Rbar haQ (inv_mem hr) (hr' _ hw')
        rw [apply_inv_apply_O, map_sub, inv_apply_apply_O] at h1
        have := neg_mem h1
        rwa [neg_sub] at this }
  suffices hRE : Rbar S g t ≤ E from (hRE hr).2 w hw
  refine sSup_le fun X hX => ?_
  obtain ⟨h, rfl, htX⟩ := hX
  intro r hrX
  have hrR : r ∈ Rbar S g t := Lbar_mul_le_Rbar htX hrX
  refine ⟨hrR, fun w hw => ?_⟩
  have hxN := mem_normalizer_of_fix haQ H.conj_ne hxM (hfix _ (cl_mem_Vt htX))
  have hxr : x * r * x⁻¹ ∈ S.Lbar ((h : G) * g) := (mem_normalizer_iff.mp hxN r).mp hrX
  set m := r⁻¹ * (x * r * x⁻¹) with hm
  have hmL : m ∈ S.Lbar ((h : G) * g) := mul_mem (inv_mem hrX) hxr
  have hxinv : ∀ v ∈ Vt S g t, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv => by
    conv_lhs => rw [← hfix v hv]
    exact inv_apply_apply_O x v
  have hmN : m ∈ Nbar S g t := by
    refine mem_Nbar.mpr ⟨mul_mem (inv_mem hrR) (Lbar_mul_le_Rbar htX hxr), fun v hv => ?_⟩
    rw [hm, coe_mul_apply, coe_mul_apply, coe_mul_apply, hxinv v hv,
      hfix _ (apply_mem_Vt_of_mem_Rbar haQ hrR hv), inv_apply_apply_O]
  obtain ⟨k, hk, hkL⟩ := hD h htX
  have hm0 : m ∈ N0bar S g t := Lbar_mul_inf_Nbar_le_N0bar hk ⟨hkL ▸ hmL, hmN⟩
  have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
    rw [hm, coe_mul_apply, coe_mul_apply, coe_mul_apply, inv_apply_apply_O, apply_inv_apply_O]
  rw [e, ← map_sub]
  exact apply_mem_Vt_of_mem_Rbar haQ hrR
    (D.N0bar_apply hm0 (hxW w hw))

theorem tri_setup (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)
    {τ₁ τ₂ : S.O} (h₁ : IsConjCent S t τ₁) (h₂ : IsConjCent S t τ₂)
    (h₃ : IsConjCent S t (t * τ₁ * τ₂)) :
    Vt S g t ⊔ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      Vt S g t ⊔ commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      (∀ w ∈ Wt S g t, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w ↔
        (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) ∧
      (∀ w ∈ Wt S g t, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w ↔
        ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) ∧
      (∀ w ∈ Wt S g t, ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) + ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) := by
  have htr := D.transitive
  have h4 := D.finrank_eq
  have hct := commSpace_t_eq H C ht ht1 hVQ
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have i₁ := h₁.inf_eq_bot H C ht ht1 hVQ htr hR
  have i₂ := h₂.inf_eq_bot H C ht ht1 hVQ htr hR
  have i₃ := h₃.inf_eq_bot H C ht ht1 hVQ htr hR
  have f₁ := h₁.finrank_commSpace H C ht ht1 hVQ
  have f₂ := h₂.finrank_commSpace H C ht ht1 hVQ
  have f₃ := h₃.finrank_commSpace H C ht ht1 hVQ
  rw [h4] at f₁ f₂ f₃
  have x₁ := h₁.fix_Vt H C ht ht1 hVQ htr hR
  have l₂ := commSpace_le_Wt_of_fix (h₂.fix_Vt H C ht ht1 hVQ htr hR)
  have l₃ := commSpace_le_Wt_of_fix (h₃.fix_Vt H C ht ht1 hVQ htr hR)
  have htW : ∀ w ∈ Wt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fun w hw => by
    rw [← hct.2, mem_fixSpace] at hw
    exact hw
  obtain ⟨e₁, e₂⟩ := sup_eq_sup_of_mul hct.1 htt h4 i₁ i₂ i₃ f₁ f₂ f₃
    (fun v hv => htW v (l₃ hv))
  refine ⟨e₂.trans e₁.symm, e₁.symm, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [fix_iff_mem_orthogonal hw, fix_iff_mem_orthogonal hw, e₁, e₂]
  · rw [fix_iff_mem_orthogonal hw, fix_iff_mem_orthogonal hw, e₁]
  · have hσσ : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) * τ₁ = 1 := by
      have := congrArg Subtype.val (h₁.mul_self H ht)
      exact this
    have hfix₁ : ∀ v ∈ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt),
        (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      intro v hv
      have hv' : v ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [← e₂.trans e₁.symm]
        exact Submodule.mem_sup_right hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv'
      rw [map_add, x₁ a ha, mem_fixSpace.mp (commSpace_le_fixSpace hσσ hb)]
    exact apply_sub_eq_add htW (fun w hw => h₁.apply_mem_Wt H C ht ht1 hVQ hw) l₂ hfix₁ hw

end Step5Data

end CFSG.LargeExtraspecial.S9.RB
