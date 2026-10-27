module

public import CFSG.LargeExtraspecial.S9RBPCaseD

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

theorem inf_le_of_le (hNo : NoA2 S g)
    (hKN : ∀ k ∈ Rbar S g t, (∀ x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t) → k ∈ Nbar S g t)
    {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hc : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹)) :
    ((Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓ fixMod S (S.Lbar g) (Vt S g t)) ⊓
      ((Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓
        fixMod S (S.Lbar ((k : G) * g)) (Vt S g t)) ≤ Vt S g t := by
  have haQ := H.conj_mem
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  obtain ⟨w₂, hw₂, h0₂, hf₂⟩ := T.exists_mem_clSub (H.mul h) (C.mul h) (cl_mem_Vt hth)
  have hthk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have hkR : S.Lbar ((k : G) * g) ≤ Rbar S g t := Lbar_mul_le_Rbar hthk
  have hcV : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t := cl_mem_Vt hthk
  set U := Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  set Fa := U ⊓ fixMod S (S.Lbar g) (Vt S g t) with hFa
  set Fk := U ⊓ fixMod S (S.Lbar ((k : G) * g)) (Vt S g t) with hFk
  have hla : ∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := fun l hl =>
    (mem_fixSub S).mp (H.fixSub_eq ▸ Submodule.mem_span_singleton_self _) l hl
  intro x hx
  by_contra hxV
  obtain ⟨⟨hxU, hxa⟩, ⟨-, hxk⟩⟩ := hx
  obtain ⟨v, hv, a, ha, rfl⟩ := Submodule.mem_sup.mp hxU
  obtain ⟨w, hw, rfl⟩ := exists_apply_sub_eq_of_mem T.inf₁ ha
  have h0 : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ 0 := fun h => hxV (by rw [h, add_zero]; exact hv)
  have hsplit : ∀ l ∈ Rbar S g t, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (v + ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w
      - w)) - (v + ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) ∈ Vt S g t →
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t := by
    intro l hl h1
    rw [map_add, show (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v + (l : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) - (v + ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) =
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) - ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) by abel]
      at h1
    have h2 := sub_mem h1 (sub_mem (apply_mem_Vt_of_mem_Rbar haQ hl hv) hv)
    rwa [add_sub_cancel_left] at h2
  have hfa : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ fixMod S (S.Lbar g) (Vt S g t) :=
    fun l hl => hsplit l (Lbar_le_Rbar ht hl) (hxa l hl)
  have hfk : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
      fixMod S (S.Lbar ((k : G) * g)) (Vt S g t) := fun l hl => hsplit l (hkR hl) (hxk l hl)
  obtain ⟨dP, hPa⟩ := T.plane (Lbar_le_Rbar ht) hw h0 hfa
  obtain ⟨-, hPk⟩ := T.plane hkR hw h0 hfk
  have dFa : finrank (ZMod 2) Fa = finrank (ZMod 2) (Vt S g t) + 2 := T.finrank_Fix hNo
  have dFk : finrank (ZMod 2) Fk = finrank (ZMod 2) Fa := by
    rw [hFk, ← T.map_Fix hk g]
    exact LinearEquiv.finrank_map_eq _ _
  have hPa' : _ ≤ Fa := hPa
  have hPk' : _ ≤ Fk := hPk
  have hFaFk : Fa ≤ Fk := by
    have hle := Submodule.finrank_mono (le_inf hPa' hPk')
    have e := Submodule.eq_of_le_of_finrank_le (inf_le_left : Fa ⊓ Fk ≤ Fa) (by omega)
    rw [← e]; exact inf_le_right
  have hFeq : Fa = Fk := Submodule.eq_of_le_of_finrank_le hFaFk (by omega)
  have hfix : ∀ l₂ ∈ S.Lbar ((k : G) * g), (l₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    intro l₂ hl₂
    set u' := (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ with hu'
    have hu'U : u' ∈ U := Submodule.mem_sup_right (sub_mem_commSpace _ _)
    have hz : (l₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u' ∈ Fa :=
      hFeq ▸ T.sub_mem_Fix (H.mul k) (C.mul k) hcV hkR hu'U hl₂
    obtain ⟨l, hl, hlz⟩ := T.exists_sub_mem hNo hKN hh hb hw₂ h0₂ hf₂ hz
    have hlR : l ∈ Rbar S g t := Lbar_le_Rbar ht hl
    have hm : l⁻¹ * l₂ ∈ Rbar S g t := mul_mem (inv_mem hlR) (hkR hl₂)
    have hmT : ∀ y ∈ Fa, ((l⁻¹ * l₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Vt S g t := by
      intro y hy
      have hyk : y ∈ Fk := hFeq ▸ hy
      have h1 := hyk.2 l₂ hl₂
      have h2 := hy.2 l⁻¹ (inv_mem hl)
      have e : ((l⁻¹ * l₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y =
          ((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) +
            (((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) := by
        rw [coe_mul_apply, map_sub]; abel
      rw [e]
      exact add_mem (apply_mem_Vt_of_mem_Rbar haQ (inv_mem hlR) h1) h2
    have hmu : ((l⁻¹ * l₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u' ∈ Vt S g t := by
      have e : ∀ y : S.Qt, ((l⁻¹ * l₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y =
          ((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) y -
            (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := by
        intro y
        rw [coe_mul_apply, map_sub, inv_apply_apply_O]
      rw [e u']
      refine apply_mem_Vt_of_mem_Rbar haQ (inv_mem hlR) ?_
      have e2 : (l₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u' =
          -(((l : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u') - ((l₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u')) := by
        abel
      rw [e2]
      exact neg_mem hlz
    have hmN := hKN _ hm (T.gen hNo hh hb hw₂ h0₂ hf₂ hm hmT hmu)
    have hma := hmN.2 _ (cl_a_mem_Vt ht)
    have e3 : l₂ = l * (l⁻¹ * l₂) := by group
    rw [e3, coe_mul_apply, hma, hla l hl]
  have hmem : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar ((k : G) * g)) := (mem_fixSub S).mpr hfix
  rw [(H.mul k).fixSub_eq] at hmem
  rcases mem_span_cl_iff.mp hmem with h | h
  · exact cl_conj_z_ne_zero S haQ H.conj_ne h
  · exact hc h.symm

end TriHyp

end CFSG.LargeExtraspecial.S9.RB
