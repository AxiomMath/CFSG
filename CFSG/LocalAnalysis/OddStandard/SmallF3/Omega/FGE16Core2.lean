module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Core1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Act

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] (T : ι → Module.End (ZMod 3) V)

theorem fgWt_map_le (e : V ≃ₗ[ZMod 3] V) (c : ι ≃ ι)
    (h : ∀ i v, T (c i) (e v) = e (T i v)) (χ : ι → ZMod 3) :
    (fgWt T χ).map (e : V →ₗ[ZMod 3] V) ≤ fgWt T (fun i => χ (c.symm i)) := by
  rintro _ ⟨v, hv, rfl⟩
  have hv' := (mem_fgWt T).mp hv
  rw [mem_fgWt]
  intro i
  have h1 := h (c.symm i) v
  rw [Equiv.apply_symm_apply] at h1
  show T i (e v) = χ (c.symm i) • e v
  rw [h1, hv' (c.symm i), map_smul]

end Generic

section Action

variable (B : Subgroup (OGroup Q)) [Fintype ↥B] [DecidableEq ↥B] (f : OGroup Q)
  (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B)

theorem fgT_conj (g : ↥B) (v : V) :
    fgT B (fgCj B f hf g) (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) v) =
      ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) (fgT B g v) := by
  show ((f * (g : OGroup Q) * f⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V)
    (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) v) = _
  simp [Subgroup.coe_mul, LinearEquiv.mul_apply, fgT]

theorem fgWt_map_f (χ : ↥B → ZMod 3) :
    (fgWt (fgT B) χ).map (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
      fgWt (fgT B) (fgPerm B (ZMod 3) (fgCj B f hf) χ) := by
  apply le_antisymm
  · exact fgWt_map_le (fgT B) ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) (fgCj B f hf).toEquiv
      (fun g v => fgT_conj B f hf g v) χ
  · intro v hv
    set e : V ≃ₗ[ZMod 3] V := ((f⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) with he
    have hfe : ∀ w : V, ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) (e w) = w := fun w => by
      show ((f * f⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) w = w
      simp
    have hef : ∀ w : V, e (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) w) = w := fun w => by
      show ((f⁻¹ * f : OGroup Q) : V ≃ₗ[ZMod 3] V) w = w
      simp
    have hint : ∀ (g : ↥B) (w : V),
        fgT B ((fgCj B f hf).toEquiv.symm g) (e w) = e (fgT B g w) := by
      intro g w
      have h1 := fgT_conj B f hf ((fgCj B f hf).toEquiv.symm g) (e w)
      rw [hfe] at h1
      have h2 : fgCj B f hf ((fgCj B f hf).toEquiv.symm g) = g := (fgCj B f hf).apply_symm_apply g
      rw [h2] at h1
      rw [h1, hef]
    have h1 := fgWt_map_le (fgT B) e (fgCj B f hf).toEquiv.symm hint
      (fgPerm B (ZMod 3) (fgCj B f hf) χ) ⟨v, hv, rfl⟩
    have h3 : (fun i => (fgPerm B (ZMod 3) (fgCj B f hf) χ)
        ((fgCj B f hf).toEquiv.symm.symm i)) = χ := by
      funext i
      simp [fgPerm_apply]
    rw [h3] at h1
    exact ⟨e v, h1, hfe v⟩

theorem finrank_fgWt_perm (χ : ↥B → ZMod 3) :
    Module.finrank (ZMod 3) (fgWt (fgT B) (fgPerm B (ZMod 3) (fgCj B f hf) χ)) =
      Module.finrank (ZMod 3) (fgWt (fgT B) χ) := by
  rw [← fgWt_map_f B f hf χ]
  exact LinearEquiv.finrank_map_eq ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) _

theorem fgWt_perm_ne_bot_iff (χ : ↥B → ZMod 3) :
    fgWt (fgT B) (fgPerm B (ZMod 3) (fgCj B f hf) χ) ≠ ⊥ ↔ fgWt (fgT B) χ ≠ ⊥ := by
  constructor
  · intro h h0
    apply h
    rw [← fgWt_map_f B f hf χ, h0, Submodule.map_bot]
  · intro h h0
    apply h
    have h1 : (fgWt (fgT B) χ).map (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) = ⊥ := by
      rw [fgWt_map_f B f hf χ]
      exact h0
    exact Submodule.map_injective_of_injective ((f : OGroup Q) : V ≃ₗ[ZMod 3] V).injective
      (by rw [h1, Submodule.map_bot])

end Action

end CFSG.OddStandard.SmallF3.Omega
