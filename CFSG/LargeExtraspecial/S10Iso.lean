module

public import CFSG.LargeExtraspecial.S10Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def PlusType4 (Q : QuadraticForm (ZMod 2) U) : Prop :=
  ∃ W : Submodule (ZMod 2) U, finrank (ZMod 2) W = 2 ∧ ∀ x ∈ W, Q x = 0

theorem exists_isometry_M2 [FiniteDimensional (ZMod 2) U] (h4 : finrank (ZMod 2) U = 4)
    {Q : QuadraticForm (ZMod 2) U} (hQ : Q.polarBilin.Nondegenerate) (hP : PlusType4 Q) :
    ∃ φ : U ≃ₗ[ZMod 2] M2, ∀ u, q₀ (φ u) = Q u := by
  set e : U ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq U (Fin 4 → ZMod 2) (by rw [h4]; simp) with he
  set Q' : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2) := Q.comp e.symm.toLinearMap with hQ'def
  have hval : ∀ x, Q' x = Q (e.symm x) := fun x => rfl
  have hpol : ∀ x y, polar Q' x y = polar Q (e.symm x) (e.symm y) := fun x y => by
    simp only [polar, hval, map_add]
  have hQ' : Q'.polarBilin.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h0 : e.symm x = 0 := hQ.1 _ fun y => by
        have := hx (e y)
        rw [polarBilin_apply_apply, hpol, e.symm_apply_apply] at this
        rwa [polarBilin_apply_apply]
      simpa using congrArg e h0
    · have h0 : e.symm x = 0 := hQ.2 _ fun y => by
        have := hx (e y)
        rw [polarBilin_apply_apply, hpol, e.symm_apply_apply] at this
        rwa [polarBilin_apply_apply]
      simpa using congrArg e h0
  obtain ⟨W, hW, hWs⟩ := hP
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q' := by
    refine ⟨W.map e.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hW]
      simp
    · rintro _ ⟨x, hx, rfl⟩
      change Q (e.symm (e x)) = 0
      rw [e.symm_apply_apply]
      exact hWs x hx
  obtain ⟨φ'⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ' (n := 2) (by simp)
    hplus
  refine ⟨e.trans (φ'.toLinearEquiv.trans plusEquiv), fun u => ?_⟩
  change q₀ (plusEquiv (φ' (e u))) = Q u
  rw [q₀_plusEquiv, φ'.map_app, hval, e.symm_apply_apply]

theorem exists_isometry_M2_base [FiniteDimensional (ZMod 2) U] (h4 : finrank (ZMod 2) U = 4)
    {Q : QuadraticForm (ZMod 2) U} (hQ : Q.polarBilin.Nondegenerate) (hP : PlusType4 Q) {a : U}
    (ha : a ≠ 0) (hQa : Q a = 0) :
    ∃ φ : U ≃ₗ[ZMod 2] M2, (∀ u, q₀ (φ u) = Q u) ∧ φ a = E00 := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isometry_M2 h4 hQ hP
  have h1 : φ₁ a ≠ 0 := fun h => ha (by simpa using congrArg φ₁.symm h)
  have h2 : qf (φ₁ a) = 0 := by rw [← q₀_apply, hφ₁, hQa]
  obtain ⟨γ, hγ⟩ := exists_act_eq_E00 _ h1 h2
  refine ⟨φ₁.trans (ρ₀ γ), fun u => ?_, hγ⟩
  change qf (act γ (φ₁ u)) = Q u
  rw [qf_act, ← q₀_apply, hφ₁]

section Transport

variable [FiniteDimensional (ZMod 2) U] {Q : QuadraticForm (ZMod 2) U}
  {φ : U ≃ₗ[ZMod 2] M2} (hφ : ∀ u, q₀ (φ u) = Q u)
include hφ

omit [FiniteDimensional (ZMod 2) U] hφ in
theorem commSpace_autCongr (g : U ≃ₗ[ZMod 2] U) :
    commSpace (LinearEquiv.autCongr φ g) = (commSpace g).map φ.toLinearMap := by
  ext m
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨g (φ.symm v) - φ.symm v, sub_mem_commSpace g _, ?_⟩
    simp
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    exact ⟨φ v, by simp⟩

theorem mem_omegaGroup_iff_autCongr (hQ : Q.polarBilin.Nondegenerate)
    (g : U ≃ₗ[ZMod 2] U) :
    g ∈ omegaGroup Q hQ ↔ LinearEquiv.autCongr φ g ∈ omegaGroup q₀ q₀_nondegenerate := by
  rw [mem_omegaGroup, mem_omegaGroup, commSpace_autCongr, LinearEquiv.finrank_map_eq,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  refine and_congr_left fun _ => ⟨fun h m => ?_, fun h u => ?_⟩
  · rw [LinearEquiv.autCongr_apply_apply, hφ, h, ← hφ, LinearEquiv.apply_symm_apply]
  · have := h (φ u)
    rwa [LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply, hφ, hφ] at this

@[expose] noncomputable def psi (φ : U ≃ₗ[ZMod 2] M2) : Gm →* (U ≃ₗ[ZMod 2] U) :=
  (LinearEquiv.autCongr φ).symm.toMonoidHom.comp ρ₀

omit [FiniteDimensional (ZMod 2) U] hφ in
theorem psi_apply (γ : Gm) (u : U) : psi φ γ u = φ.symm (act γ (φ u)) := by
  simp [psi]

omit [FiniteDimensional (ZMod 2) U] hφ in
theorem psi_injective : Function.Injective (psi φ) :=
  (LinearEquiv.autCongr φ).symm.injective.comp ρ₀_injective

theorem range_psi (hQ : Q.polarBilin.Nondegenerate) : (psi φ).range = omegaGroup Q hQ := by
  ext g
  rw [mem_omegaGroup_iff_autCongr hφ hQ, ← range_ρ₀, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, by simp [psi]⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, by rw [psi, MonoidHom.comp_apply, hγ]; simp⟩

end Transport

end CFSG.LargeExtraspecial.S10
