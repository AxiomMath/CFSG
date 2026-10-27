module

public import CFSG.LargeExtraspecial.S9RBTriC
public import CFSG.LargeExtraspecial.S9RBPa
public import CFSG.LargeExtraspecial.S9RBSimple
public import CFSG.LargeExtraspecial.S9RBTriB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Tri

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hA6 : A6Case H C ht ht1 hVQ)
  (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)
include hCE H hNo C ht ht1 hVQ hA6 hR

theorem false_of_triangle {τ₁ τ₂ : S.O} (h₁ : IsConjCent S t τ₁) (h₂ : IsConjCent S t τ₂)
    (h₃ : IsConjCent S t (t * τ₁ * τ₂)) : False := by
  obtain ⟨e₂, -, hf₂, hf₃, hD⟩ := tri_setup H C ht ht1 hVQ hA6 hR h₁ h₂ h₃
  set τ₃ := t * τ₁ * τ₂ with hτ₃
  have haQ := H.conj_mem
  have htr := hA6.transitive
  have i₁ := h₁.inf_eq_bot H C ht ht1 hVQ htr hR
  have i₂ := h₂.inf_eq_bot H C ht ht1 hVQ htr hR
  have i₃ := h₃.inf_eq_bot H C ht ht1 hVQ htr hR
  have x₁ := h₁.fix_Vt H C ht ht1 hVQ htr hR
  have x₂ := h₂.fix_Vt H C ht ht1 hVQ htr hR
  have q₁ := fun r (hr : r ∈ Rbar S g t) w (hw : w ∈ Wt S g t) =>
    apply_sub_mem_Vt_of_fix H C ht ht1 hVQ hA6 (h₁.mem_Mbar ht) h₁.comm x₁ hr hw
  have q₂ := fun r (hr : r ∈ Rbar S g t) w (hw : w ∈ Wt S g t) =>
    apply_sub_mem_Vt_of_fix H C ht ht1 hVQ hA6 (h₂.mem_Mbar ht) h₂.comm x₂ hr hw
  have hRV : ∀ r ∈ Rbar S g t, ∀ v ∈ Vt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t :=
    fun r hr v hv => apply_mem_Vt_of_mem_Rbar haQ hr hv
  have hRW : ∀ r ∈ Rbar S g t, ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t :=
    fun r hr w hw => apply_mem_Wt H hr hw
  have l₁ := commSpace_le_Wt_of_fix x₁
  have l₂ := commSpace_le_Wt_of_fix x₂
  set U := Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  have hUW : U ≤ Wt S g t := sup_le (Vt_le_Wt H ht1) l₁
  have hRU : ∀ r ∈ Rbar S g t, ∀ x ∈ U, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ U := by
    intro r hr x hx
    obtain ⟨v, hv, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨w, hw, rfl⟩ := exists_apply_sub_eq_of_mem i₁ ha
    rw [map_add, map_sub]
    have e : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v + ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) v - ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) +
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
          (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by abel
    rw [e]
    exact add_mem (Submodule.mem_sup_left (sub_mem (hRV r hr v hv) (q₁ r hr w hw)))
      (Submodule.mem_sup_right (sub_mem_commSpace _ _))
  have hnot : ∀ w ∈ Wt S g t, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ 0 →
      (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∉ Vt S g t ∧
        (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∉ Vt S g t ∧
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) + ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∉
          Vt S g t := by
    intro w hw h0
    have hτw : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := fun e => h0 (by rw [e, sub_self])
    refine ⟨fun hv => h0 ?_, fun hv => hτw ?_, fun hv => hτw ?_⟩
    · have : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
          Vt S g t ⊓ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hv, sub_mem_commSpace _ _⟩
      rwa [i₁, Submodule.mem_bot] at this
    · have : (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
          Vt S g t ⊓ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hv, sub_mem_commSpace _ _⟩
      rw [i₂, Submodule.mem_bot, sub_eq_zero] at this
      exact (hf₂ w hw).mpr this
    · rw [← hD w hw] at hv
      have : (τ₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
          Vt S g t ⊓ commSpace (τ₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hv, sub_mem_commSpace _ _⟩
      rw [i₃, Submodule.mem_bot, sub_eq_zero] at this
      exact (hf₃ w hw).mpr this
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  have hbQ := conj_mem_QG' S h.2 haQ
  have hbV : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t := cl_mem_Vt hth
  have haV : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
  have hbV' : (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hbV
  have hPI := pairInt_of_radBound H C ht ht1 hVQ
    (radBound_of_tau_not_mem H C ht ht1 hVQ hA6.tau_not_mem)
  have hP := clSub_inf_clSub_le_Vt_a6 H C ht ht1 hVQ hA6 hh hb
  have hCab := sup_Vt_inf_sup_Vt H C ht ht1 hVQ hh hb hP
  have hCa := fun w (hw : w ∈ Wt S g t) =>
    (forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hw).mp
  have hCb := fun w (hw : w ∈ Wt S g t) =>
    (forall_apply_sub_mem_Vt_iff_b H hNo C ht ht1 hVQ hh hb hPI hw).mp
  have f₁ := h₁.finrank_commSpace H C ht ht1 hVQ
  rw [hA6.finrank_eq] at f₁
  have hτ₁M := h₁.mem_Mbar ht
  have k₁ := two_le_finrank_commSpace_inf_clSub H C hτ₁M (x₁ _ (cl_a_mem_Vt ht)) f₁
  have k₂ := two_le_finrank_commSpace_inf_clSub (H.mul h) (C.mul h) hτ₁M (x₁ _ hbV) f₁
  have hne₁ : commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ S.clSub (S.QG ⊓ S.Qa g) ≠ ⊥ :=
    fun h0 => by rw [h0, finrank_bot] at k₁; omega
  have hne₂ : commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≠ ⊥ :=
    fun h0 => by rw [h0, finrank_bot] at k₂; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₁
  obtain ⟨u', hu', hu'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₂
  obtain ⟨w₁, hw₁, hw₁u⟩ := exists_apply_sub_eq_of_mem i₁ hu.1
  obtain ⟨w₂, hw₂, hw₂u⟩ := exists_apply_sub_eq_of_mem i₁ hu'.1
  obtain ⟨n₁, n₂, n₃⟩ := hnot w₁ hw₁ (by rw [hw₁u]; exact hu0)
  obtain ⟨n₁', n₂', n₃'⟩ := hnot w₂ hw₂ (by rw [hw₂u]; exact hu'0)
  rw [hw₁u] at n₁ n₃
  rw [hw₂u] at n₁' n₃'
  have htrans : ∀ k ∈ Rbar S g t, ∀ w ∈ Wt S g t,
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
          ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t →
        (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
          ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t :=
    fun k hk w hw hkw => apply_sub_mem_of_transfer (hRW k hk) (q₁ k hk) (q₂ k hk) i₁
      (fun w hw => (hf₂ w hw).mp) hw hkw
  have hy₁ := hCa _ (l₂ (sub_mem_commSpace _ w₁)) fun l hl =>
    htrans l (Lbar_le_Rbar ht hl) w₁ hw₁
      (by rw [hw₁u]; exact haV (Lbar_apply_sub_mem_span' haQ hu.2 hl))
  have hy₂ := hCb _ (l₂ (sub_mem_commSpace _ w₂)) fun l hl =>
    htrans l (Lbar_mul_le_Rbar hth hl) w₂ hw₂
      (by rw [hw₂u]; exact hbV' (Lbar_apply_sub_mem_span' hbQ hu'.2 hl))
  have huCa : u ∈ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t :=
    Submodule.mem_sup_left ⟨hu.2, l₁ hu.1⟩
  have hu'Cb : u' ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t :=
    Submodule.mem_sup_left ⟨hu'.2, l₁ hu'.1⟩
  have huU : u ∈ U := Submodule.mem_sup_right hu.1
  have hu'U : u' ∈ U := Submodule.mem_sup_right hu'.1
  have hyU : ∀ w, (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ U := fun w => by
    rw [← e₂]; exact Submodule.mem_sup_right (sub_mem_commSpace _ _)
  set Ta := Vt S g t ⊔ (ZMod 2) ∙ u ⊔ (ZMod 2) ∙ ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁)
    with hTa
  set Tb := Vt S g t ⊔ (ZMod 2) ∙ u' ⊔ (ZMod 2) ∙ ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂)
    with hTb
  have dTa : finrank (ZMod 2) Ta = finrank (ZMod 2) (Vt S g t) + 2 :=
    finrank_sup_span_pair n₁ n₂ n₃
  have dTb : finrank (ZMod 2) Tb = finrank (ZMod 2) (Vt S g t) + 2 :=
    finrank_sup_span_pair n₁' n₂' n₃'
  have hTaC : Ta ≤ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t :=
    sup_le (sup_le le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).mpr huCa))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hy₁)
  have hTbC : Tb ≤ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t :=
    sup_le (sup_le le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).mpr hu'Cb))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hy₂)
  have hTab : Ta ⊓ Tb ≤ Vt S g t := hCab ▸ inf_le_inf hTaC hTbC
  have dTab := Submodule.finrank_mono hTab
  have dsum := Submodule.finrank_sup_add_finrank_inf_eq Ta Tb
  have hTU : Ta ⊔ Tb ≤ U := by
    refine sup_le (sup_le (sup_le le_sup_left ?_) ?_) (sup_le (sup_le le_sup_left ?_) ?_)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr huU
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (hyU w₁)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hu'U
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (hyU w₂)
  have dU : finrank (ZMod 2) U = 8 := by
    rw [hU, finrank_sup_of_inf_eq_bot i₁, hA6.finrank_eq, f₁]
  have h4 := hA6.finrank_eq
  have hTeq : Ta ⊔ Tb = U := Submodule.eq_of_le_of_finrank_le hTU (by omega)
  have hgen : ∀ k ∈ Rbar S g t, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t →
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u' ∈ Vt S g t →
        ∀ v ∈ U, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := by
    intro k hk hku hku' v hv
    set F := (Vt S g t).comap ((k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id)
      with hF
    have hmemF : ∀ x, x ∈ F ↔ (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := fun x => by
      simp [hF]
    have hVF : Vt S g t ≤ F := fun x hx => (hmemF x).mpr (sub_mem (hRV k hk x hx) hx)
    have g₁ := (hmemF _).mpr (htrans k hk w₁ hw₁ (by rw [hw₁u]; exact hku))
    have g₂ := (hmemF _).mpr (htrans k hk w₂ hw₂ (by rw [hw₂u]; exact hku'))
    have hle : Ta ⊔ Tb ≤ F := by
      refine sup_le (sup_le (sup_le hVF ?_) ?_) (sup_le (sup_le hVF ?_) ?_)
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr ((hmemF u).mpr hku)
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr g₁
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr ((hmemF u').mpr hku')
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr g₂
    rw [← hTeq] at hv
    exact (hmemF v).mp (hle hv)
  have hidx := index_le_of_gen (X := Rbar S g t) (le_sup_left : Vt S g t ≤ U) hRV hRU huU
    hu'U hgen (K := kerQuot S (Rbar S g t) U (Vt S g t) hRU) fun k => Iff.rfl
  rw [dU, h4] at hidx
  have hlt : (kerQuot S (Rbar S g t) U (Vt S g t) hRU).index < 360 := by
    norm_num at hidx; omega
  have hN0 : ∀ x : Rbar S g t, (x : S.O) ∈ N0bar S g t →
      x ∈ kerQuot S (Rbar S g t) U (Vt S g t) hRU :=
    fun x hx v hv => N0bar_apply_sub_mem_Vt_a6 H C ht ht1 hVQ hA6 hx (hUW hv)
  have hLK : ∀ l ∈ S.Lbar g, ∀ v ∈ U, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t :=
    fun l hl v hv => (mem_of_index_lt_a6 hCE H C ht ht1 hVQ hA6
      (normal_kerQuot hRU hRV) hN0 hlt (x := ⟨l, Lbar_le_Rbar ht hl⟩)
      (Subtype.ext (mul_self_of_mem_Lbar S haQ hl))) v hv
  have hu'Ca := hCa u' (hUW hu'U) fun l hl => hLK l hl u' hu'U
  exact n₁' (hCab ▸ ⟨hu'Ca, hu'Cb⟩)

end Tri

end CFSG.LargeExtraspecial.S9.RB
