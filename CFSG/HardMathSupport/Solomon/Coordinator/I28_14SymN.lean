module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymComm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal Module

theorem i28_14_isF2Transvection_conj {H : Type} [AddCommGroup H] [Module (ZMod 2) H]
    (g : LinearMap.GeneralLinearGroup (ZMod 2) H) {t : LinearMap.GeneralLinearGroup (ZMod 2) H}
    (ht : IsF2Transvection t) : IsF2Transvection (g * t * g⁻¹) := by
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  have hgi : ∀ v : H, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) H) : H →ₗ[ZMod 2] H)
      ((g : H →ₗ[ZMod 2] H) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  have h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) H) : H →ₗ[ZMod 2] H))
      ((g : H →ₗ[ZMod 2] H) a) = 0 := by
    rw [LinearMap.comp_apply, hgi, h]
  refine (isF2Transvection_iff _).mpr ⟨_, _, h', ?_, ?_, conj_tv g φ a h h'⟩
  · intro h0
    apply hφ
    ext x
    have := LinearMap.congr_fun h0 ((g : H →ₗ[ZMod 2] H) x)
    rw [LinearMap.comp_apply, hgi] at this
    simpa using this
  · intro h0
    apply ha
    have := congrArg (fun v => ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) H) :
      H →ₗ[ZMod 2] H) v) h0
    simpa [hgi, map_zero] using this

variable {m : ℕ} {H : Type} [AddCommGroup H] [Module (ZMod 2) H] (M : SymModel m H)

theorem i28_14_symModel_N (hm : 5 ≤ m)
    (haut : ∀ α : MulAut (Equiv.Perm (Fin m)),
      (∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (Equiv.swap i j) = Equiv.swap a b) →
        ∃ π : Equiv.Perm (Fin m), α = MulAut.conj π)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) H}
    (hg : ∀ x ∈ M.ψ.range, g * x * g⁻¹ ∈ M.ψ.range) : g ∈ M.ψ.range := by
  let e : Equiv.Perm (Fin m) ≃* M.ψ.range := MonoidHom.ofInjective M.inj
  let κ : M.ψ.range →* M.ψ.range :=
    ((MulAut.conj g).toMonoidHom.comp M.ψ.range.subtype).codRestrict M.ψ.range
      (fun x => hg x.1 x.2)
  let α₀ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m) :=
    e.symm.toMonoidHom.comp (κ.comp e.toMonoidHom)
  have hα₀ : ∀ σ, M.ψ (α₀ σ) = g * M.ψ σ * g⁻¹ := by
    intro σ
    have h1 : e (α₀ σ) = κ (e σ) := by
      change e (e.symm (κ (e σ))) = _
      exact e.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    exact h2
  have hinj : Function.Injective α₀ := by
    intro σ τ h
    apply M.inj
    have := hα₀ σ
    rw [h, hα₀ τ] at this
    exact mul_right_cancel (mul_left_cancel this.symm)
  let α : MulAut (Equiv.Perm (Fin m)) := MulEquiv.ofBijective α₀ (Finite.injective_iff_bijective.mp hinj)
  have hαswap : ∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (Equiv.swap i j) = Equiv.swap a b := by
    intro i j hij
    have hT : IsF2Transvection (M.ψ (α₀ (Equiv.swap i j))) := by
      rw [hα₀]
      exact i28_14_isF2Transvection_conj g (i28_14_symModel_swap_isTv M (by omega) hij)
    obtain ⟨a, b, hab, hs⟩ := i28_14_symModel_swap_of_transv M hm hT
    exact ⟨a, b, hab, hs⟩
  obtain ⟨π, hπ⟩ := haut α hαswap
  have hconj : ∀ σ, α₀ σ = π * σ * π⁻¹ := fun σ => by
    have := congrArg (fun f : MulAut (Equiv.Perm (Fin m)) => f σ) hπ
    exact this
  have hc : ∀ σ, (M.ψ π)⁻¹ * g * M.ψ σ = M.ψ σ * ((M.ψ π)⁻¹ * g) := by
    intro σ
    have h := hα₀ σ
    rw [hconj, map_mul, map_mul, map_inv] at h
    have h' : g * M.ψ σ = M.ψ π * M.ψ σ * (M.ψ π)⁻¹ * g := by
      calc g * M.ψ σ = (g * M.ψ σ * g⁻¹) * g := by group
        _ = _ := by rw [← h]
    calc (M.ψ π)⁻¹ * g * M.ψ σ = (M.ψ π)⁻¹ * (g * M.ψ σ) := by group
      _ = (M.ψ π)⁻¹ * (M.ψ π * M.ψ σ * (M.ψ π)⁻¹ * g) := by rw [h']
      _ = _ := by group
  have h1 := i28_14_symModel_eq_one_of_comm M (by omega) _ hc
  have : g = M.ψ π := by
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  exact ⟨π, this.symm⟩

end CFSG.HardMathSupport.Solomon.Coordinator
