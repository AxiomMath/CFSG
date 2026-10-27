module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.GH71.S55

variable {Y Γ : Type*} [Group Y] [Group Γ]

@[expose] def NormalizesPSub (ℓ : ℕ) (α : MulAut Y) : Prop :=
  ∃ R : Subgroup Y, R ≠ ⊥ ∧ IsPGroup ℓ R ∧ R.map α.toMonoidHom = R

@[expose] def FixesInvolution (α : MulAut Y) : Prop :=
  ∃ t : Y, orderOf t = 2 ∧ α t = t

theorem normalizesPSub_of_congr (e : Y ≃* Γ) {ℓ : ℕ} {α : MulAut Y}
    (h : NormalizesPSub ℓ (MulAut.congr e α)) : NormalizesPSub ℓ α := by
  obtain ⟨R, hR1, hRp, hRα⟩ := h
  refine ⟨R.map e.symm.toMonoidHom, fun hb => hR1 ?_, hRp.map _, ?_⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective R (f := e.symm.toMonoidHom)
      e.symm.injective).1 hb
  · have hc : α.toMonoidHom.comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp (MulAut.congr e α).toMonoidHom := by
      ext x
      change α (e.symm x) = e.symm (e (α (e.symm (x))))
      rw [e.symm_apply_apply]
    rw [Subgroup.map_map, hc, ← Subgroup.map_map, hRα]

theorem fixesInvolution_of_congr (e : Y ≃* Γ) {α : MulAut Y}
    (h : FixesInvolution (MulAut.congr e α)) : FixesInvolution α := by
  obtain ⟨t, ht2, htα⟩ := h
  refine ⟨e.symm t, by rw [MulEquiv.orderOf_eq]; exact ht2, ?_⟩
  have h1 : e (α (e.symm t)) = t := htα
  calc α (e.symm t) = e.symm (e (α (e.symm t))) := (e.symm_apply_apply _).symm
    _ = e.symm t := by rw [h1]

theorem normalizesPSub_of_conj {ℓ : ℕ} {α : MulAut Y} (γ : MulAut Y)
    (h : NormalizesPSub ℓ (γ * α * γ⁻¹)) : NormalizesPSub ℓ α :=
  normalizesPSub_of_congr γ h

theorem fixesInvolution_of_conj {α : MulAut Y} (γ : MulAut Y)
    (h : FixesInvolution (γ * α * γ⁻¹)) : FixesInvolution α :=
  fixesInvolution_of_congr γ h

theorem orderOf_congr (e : Y ≃* Γ) (α : MulAut Y) : orderOf (MulAut.congr e α) = orderOf α :=
  MulEquiv.orderOf_eq (MulAut.congr e) α

theorem congr_conj_eq (e : Y ≃* Γ) (g : Y) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  change e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem congr_not_mem_range_conj (e : Y ≃* Γ) {α : MulAut Y}
    (h : α ∉ (MulAut.conj : Y →* MulAut Y).range) :
    MulAut.congr e α ∉ (MulAut.conj : Γ →* MulAut Γ).range := by
  rintro ⟨g, hg⟩
  refine h ⟨e.symm g, (MulAut.congr e).injective ?_⟩
  rw [congr_conj_eq, e.apply_symm_apply]
  exact hg

end CFSG.OddStandard.GH71.S55
