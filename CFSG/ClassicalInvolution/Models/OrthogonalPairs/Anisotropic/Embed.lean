module

public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Field

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Models

variable {K K' V : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'} [AddCommGroup V]
  [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def suEnd : SUid σ 3 →* Module.End K (Fin 3 → K') where
  toFun g :=
    { toFun := fun v => g • v
      map_add' := fun v w => smul_add g v w
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul K' c v, smul_comm, algebraMap_smul] }
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp [mul_smul]

theorem suEnd_apply (g : SUid σ 3) (v : Fin 3 → K') : suEnd (K := K) g v = g • v := rfl

structure UnitaryEmbedding (Q : QuadraticForm K V) (σ : K' ≃+* K') where
  incl : (Fin 3 → K') →ₗ[K] V
  coords : V →ₗ[K] (Fin 3 → K')
  Q_incl : ∀ x, algebraMap K K' (Q (incl x)) = herm σ x x
  coords_incl : ∀ x, coords (incl x) = x
  polar_coords : ∀ z y, polar Q (incl z) y = polar Q (incl z) (incl (coords y))

namespace UnitaryEmbedding

variable (D : UnitaryEmbedding Q σ)

@[expose] def embLin (S : Module.End K (Fin 3 → K')) : V →ₗ[K] V :=
  LinearMap.id + D.incl ∘ₗ (S - 1) ∘ₗ D.coords

theorem embLin_apply (S : Module.End K (Fin 3 → K')) (x : V) :
    D.embLin S x = x + D.incl (S (D.coords x) - D.coords x) := by
  simp [embLin]

theorem embLin_one : D.embLin 1 = 1 := by
  ext x
  simp [embLin_apply]

theorem embLin_mul (S T : Module.End K (Fin 3 → K')) :
    D.embLin (S * T) = D.embLin S * D.embLin T := by
  ext x
  simp only [embLin_apply, Module.End.mul_apply, map_add, D.coords_incl, map_sub]
  abel

theorem embLin_apply_eq (S : Module.End K (Fin 3 → K')) (x : V) :
    D.embLin S x = D.incl (S (D.coords x)) + (x - D.incl (D.coords x)) := by
  rw [embLin_apply, map_sub]
  abel

theorem polar_incl_sub (z : Fin 3 → K') (x : V) :
    polar Q (D.incl z) (x - D.incl (D.coords x)) = 0 := by
  rw [polar_sub_right, D.polar_coords z x, sub_self]

theorem Q_embLin {S : Module.End K (Fin 3 → K')} (hS : ∀ z, herm σ (S z) (S z) = herm σ z z)
    (x : V) : Q (D.embLin S x) = Q x := by
  have hx : x = D.incl (D.coords x) + (x - D.incl (D.coords x)) := by abel
  have hQ : Q (D.incl (S (D.coords x))) = Q (D.incl (D.coords x)) := by
    apply (algebraMap K K').injective
    rw [D.Q_incl, D.Q_incl, hS]
  rw [D.embLin_apply_eq, QuadraticMap.map_add Q, D.polar_incl_sub, hQ]
  conv_rhs => rw [hx]
  rw [QuadraticMap.map_add Q, D.polar_incl_sub]

@[expose] noncomputable def embHom {G : Type*} [Group G] (ρ : G →* Module.End K (Fin 3 → K')) :
    G →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.ofLinearMap (D.embLin (ρ g)) (D.embLin (ρ g⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, mul_inv_cancel, map_one, embLin_one]
      rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, inv_mul_cancel, map_one, embLin_one]
      rfl)
  map_one' := by
    refine LinearEquiv.ext fun x => ?_
    simp [embLin_one]
  map_mul' g h := by
    refine LinearEquiv.ext fun x => ?_
    simp [embLin_mul]

theorem embHom_apply {G : Type*} [Group G] (ρ : G →* Module.End K (Fin 3 → K')) (g : G) (x : V) :
    D.embHom ρ g x = D.embLin (ρ g) x :=
  rfl

@[expose] noncomputable def theta : SUid σ 3 →* (V ≃ₗ[K] V) :=
  D.embHom suEnd

theorem theta_apply (g : SUid σ 3) (x : V) :
    D.theta g x = x + D.incl (g • D.coords x - D.coords x) :=
  D.embLin_apply (suEnd g) x

theorem theta_incl (g : SUid σ 3) (z : Fin 3 → K') : D.theta g (D.incl z) = D.incl (g • z) := by
  rw [theta_apply, D.coords_incl, map_sub]
  abel

theorem theta_injective : Function.Injective (D.theta : SUid σ 3 → V ≃ₗ[K] V) := by
  intro g h hgh
  apply ext_smul σ
  intro v
  have := congrArg (fun t : V ≃ₗ[K] V => D.coords (t (D.incl v))) hgh
  simpa [theta_incl, D.coords_incl] using this

theorem theta_mem_orthogonalGroup (g : SUid σ 3) :
    D.theta g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  exact D.Q_embLin (S := suEnd g) (fun z => herm_smul_smul σ g z z) x

end UnitaryEmbedding


structure NormTriple (Q : QuadraticForm K V) (σ : K' ≃+* K') where
  φ : Fin 3 → (K' →ₗ[K] V)
  Q_φ : ∀ j x, algebraMap K K' (Q (φ j x)) = σ x * x
  orth : ∀ j k, j ≠ k → ∀ x y, polar Q (φ j x) (φ k y) = 0

namespace NormTriple

variable (T : NormTriple Q σ)

@[expose] def incl : (Fin 3 → K') →ₗ[K] V :=
  ∑ j, T.φ j ∘ₗ (LinearMap.proj j : (Fin 3 → K') →ₗ[K] K')

theorem incl_apply (x : Fin 3 → K') : T.incl x = T.φ 0 (x 0) + T.φ 1 (x 1) + T.φ 2 (x 2) := by
  simp [incl, Fin.sum_univ_three]

theorem Q_incl (x : Fin 3 → K') : algebraMap K K' (Q (T.incl x)) = herm σ x x := by
  have h01 := T.orth 0 1 (by decide) (x 0) (x 1)
  have h02 := T.orth 0 2 (by decide) (x 0) (x 2)
  have h12 := T.orth 1 2 (by decide) (x 1) (x 2)
  rw [incl_apply, QuadraticMap.map_add Q, QuadraticMap.map_add Q, polar_add_left, h01, h02, h12]
  simp only [map_add, add_zero, T.Q_φ, herm, Fin.sum_univ_three]

theorem polar_incl (hσ : ∀ c, σ (σ c) = c) (x y : Fin 3 → K') :
    algebraMap K K' (polar Q (T.incl x) (T.incl y)) = herm σ x y + σ (herm σ x y) := by
  have h := T.Q_incl (x + y)
  rw [map_add, QuadraticMap.map_add Q, map_add, map_add, T.Q_incl, T.Q_incl] at h
  rw [herm_add_left, herm_add_right, herm_add_right, herm_conj σ hσ x y] at h
  linear_combination h

theorem eq_zero_of_polar (hσ : IsUnitaryInvolution σ) {x : Fin 3 → K'}
    (h : ∀ y, polar Q (T.incl x) (T.incl y) = 0) : x = 0 := by
  funext j
  by_contra hj
  have hσj : σ (x j) ≠ 0 := (map_ne_zero σ).mpr hj
  obtain ⟨c, hc⟩ := hσ.trace_surj 1 (map_one σ)
  have h1 := T.polar_incl hσ.invol x (Pi.single j (c / σ (x j)))
  rw [h, map_zero, herm_single_right] at h1
  have h2 : σ (x j) * (c / σ (x j)) = c := by field_simp
  rw [h2] at h1
  rw [hc] at h1
  exact one_ne_zero h1.symm

theorem incl_injective (hσ : IsUnitaryInvolution σ) : Function.Injective T.incl := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact T.eq_zero_of_polar hσ fun y => by rw [hx, polar_zero_left]

theorem isCompl (hσ : IsUnitaryInvolution σ) [FiniteDimensional K V] :
    IsCompl (LinearMap.range T.incl)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.range T.incl)) := by
  rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (QuadraticMap.isSymm_polarBilin Q).isRefl]
  rw [Submodule.disjoint_def]
  rintro _ ⟨z, rfl⟩ hz
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hz
  have : z = 0 := T.eq_zero_of_polar hσ fun y => by
    have := hz (T.incl y) ⟨y, rfl⟩
    rw [polarBilin_apply_apply, polar_comm] at this
    exact this
  rw [this, map_zero]

@[expose] noncomputable def toEmbedding [FiniteDimensional K V] (hσ : IsUnitaryInvolution σ) :
    UnitaryEmbedding Q σ where
  incl := T.incl
  coords := (LinearEquiv.ofInjective T.incl (T.incl_injective hσ)).symm.toLinearMap ∘ₗ
    Submodule.projectionOnto _ _ (T.isCompl hσ)
  Q_incl := T.Q_incl
  coords_incl x := by
    have hmem : T.incl x ∈ LinearMap.range T.incl := ⟨x, rfl⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Submodule.projectionOnto_apply_of_mem_left (T.isCompl hσ) hmem]
    exact (LinearEquiv.symm_apply_eq _).mpr rfl
  polar_coords z y := by
    have hc := T.isCompl hσ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hsymm : ∀ w : LinearMap.range T.incl, T.incl
        ((LinearEquiv.ofInjective T.incl (T.incl_injective hσ)).symm w) = w := fun w =>
      congrArg Subtype.val
        (LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective T.incl (T.incl_injective hσ)) w)
    rw [hsymm, Submodule.coe_projectionOnto_apply]
    have hy : y - (LinearMap.range T.incl).projection _ hc y ∈
        LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.range T.incl) :=
      Submodule.sub_projection_mem hc y
    have := LinearMap.BilinForm.mem_orthogonal_iff.mp hy (T.incl z) ⟨z, rfl⟩
    rw [polarBilin_apply_apply, polar_sub_right, sub_eq_zero] at this
    exact this

end NormTriple


namespace UnitaryEmbedding

variable (D : UnitaryEmbedding Q σ)

@[expose] def twist (τ : (Fin 3 → K') ≃ₗ[K] (Fin 3 → K'))
    (hτ : ∀ x, herm σ (τ x) (τ x) = herm σ x x) : UnitaryEmbedding Q σ where
  incl := D.incl ∘ₗ τ.toLinearMap
  coords := τ.symm.toLinearMap ∘ₗ D.coords
  Q_incl x := by simp [D.Q_incl, hτ]
  coords_incl x := by simp [D.coords_incl]
  polar_coords z y := by simp [D.polar_coords (τ z) y]

theorem twist_embLin (τ : (Fin 3 → K') ≃ₗ[K] (Fin 3 → K'))
    (hτ : ∀ x, herm σ (τ x) (τ x) = herm σ x x) (S : Module.End K (Fin 3 → K')) :
    (D.twist τ hτ).embLin S = D.embLin (τ.toLinearMap ∘ₗ S ∘ₗ τ.symm.toLinearMap) := by
  ext x
  simp [embLin_apply, twist]

end UnitaryEmbedding

section Flip

variable (E : QuadExt K K' σ)

@[expose] def QuadExt.sigmaEquiv : K' ≃ₗ[K] K' where
  toFun := σ
  map_add' := map_add σ
  map_smul' c x := by simp [Algebra.smul_def, E.fix]
  invFun := σ
  left_inv := E.isUnitary.invol
  right_inv := E.isUnitary.invol

@[expose] def QuadExt.flipAt (j : Fin 3) : (Fin 3 → K') ≃ₗ[K] (Fin 3 → K') :=
  LinearEquiv.piCongrRight fun i => if i = j then E.sigmaEquiv else LinearEquiv.refl K K'

theorem QuadExt.flipAt_apply (j : Fin 3) (x : Fin 3 → K') (i : Fin 3) :
    E.flipAt j x i = if i = j then σ (x i) else x i := by
  by_cases h : i = j <;> simp [flipAt, h, QuadExt.sigmaEquiv]

theorem QuadExt.herm_flipAt (j : Fin 3) (x : Fin 3 → K') :
    herm σ (E.flipAt j x) (E.flipAt j x) = herm σ x x := by
  simp only [herm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [E.flipAt_apply]
  by_cases h : i = j
  · simp [h, E.isUnitary.invol, mul_comm]
  · simp [h]

end Flip

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
