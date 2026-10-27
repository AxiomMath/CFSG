module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSemilinear

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Matrix Module CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization

section Gamma

variable {k : Type*} [Field k]

@[expose] def semilinPerm (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k) :
    Equiv.Perm (Fin 2 → k) where
  toFun w := A • (fun i => σ (w i))
  invFun w := fun i => σ.symm ((A⁻¹ • w) i)
  left_inv w := by
    funext i
    have h : A⁻¹ • (A • (fun j => σ (w j))) = fun j => σ (w j) := inv_smul_smul A _
    simp only [h, RingEquiv.symm_apply_apply]
  right_inv w := by
    have h : (fun i => σ (σ.symm ((A⁻¹ • w) i))) = A⁻¹ • w := funext fun i => σ.apply_symm_apply _
    show A • (fun i => σ (σ.symm ((A⁻¹ • w) i))) = w
    rw [h]
    exact smul_inv_smul A w

theorem semilinPerm_apply (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k) (w : Fin 2 → k) :
    semilinPerm A σ w = A • (fun i => σ (w i)) := rfl

theorem comp_smul_eq (σ : k ≃+* k) (A : SpecialLinearGroup (Fin 2) k) (v : Fin 2 → k) :
    (fun i => σ ((A • v) i)) =
      SpecialLinearGroup.map (σ : k →+* k) A • (fun i => σ (v i)) := by
  funext i
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def]
  have := RingHom.map_mulVec (σ : k →+* k) (A : Matrix (Fin 2) (Fin 2) k) v i
  simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem semilinPerm_mul (A₁ A₂ : SpecialLinearGroup (Fin 2) k) (σ₁ σ₂ : k ≃+* k) :
    semilinPerm A₁ σ₁ * semilinPerm A₂ σ₂ =
      semilinPerm (A₁ * SpecialLinearGroup.map (σ₁ : k →+* k) A₂) (σ₁ * σ₂) := by
  ext w : 1
  show A₁ • (fun i => σ₁ ((A₂ • (fun j => σ₂ (w j))) i)) = _
  rw [comp_smul_eq, ← mul_smul]
  rfl

theorem semilinPerm_one : semilinPerm (1 : SpecialLinearGroup (Fin 2) k) 1 = 1 := by
  ext w : 1
  show (1 : SpecialLinearGroup (Fin 2) k) • (fun i => (1 : k ≃+* k) (w i)) = w
  rw [one_smul]
  rfl

theorem map_symm_map (σ : k ≃+* k) (A : SpecialLinearGroup (Fin 2) k) :
    SpecialLinearGroup.map (σ : k →+* k) (SpecialLinearGroup.map (σ.symm : k →+* k) A) = A := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

@[expose] def Gamma (k : Type*) [Field k] : Subgroup (Equiv.Perm (Fin 2 → k)) where
  carrier := {g | ∃ (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k), g = semilinPerm A σ}
  one_mem' := ⟨1, 1, semilinPerm_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨A₁, σ₁, rfl⟩ ⟨A₂, σ₂, rfl⟩
    exact ⟨_, _, semilinPerm_mul A₁ A₂ σ₁ σ₂⟩
  inv_mem' := by
    rintro _ ⟨A, σ, rfl⟩
    refine ⟨SpecialLinearGroup.map (σ.symm : k →+* k) A⁻¹, σ.symm, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    have hσ : σ * σ.symm = 1 := RingEquiv.ext fun x => by simp
    rw [semilinPerm_mul, map_symm_map, mul_inv_cancel, hσ, semilinPerm_one]

theorem mem_Gamma {g : Equiv.Perm (Fin 2 → k)} :
    g ∈ Gamma k ↔ ∃ (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k), g = semilinPerm A σ :=
  Iff.rfl

theorem semilinPerm_mem (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k) :
    semilinPerm A σ ∈ Gamma k := ⟨A, σ, rfl⟩

theorem semilinPerm_add (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k) (x y : Fin 2 → k) :
    semilinPerm A σ (x + y) = semilinPerm A σ x + semilinPerm A σ y := by
  have h : (fun i => σ ((x + y) i)) = (fun i => σ (x i)) + (fun i => σ (y i)) := by
    funext i; simp
  rw [semilinPerm_apply, semilinPerm_apply, semilinPerm_apply, h]
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def,
    Matrix.SpecialLinearGroup.smul_def]
  simp [Matrix.mulVec_add]

theorem semilinPerm_isSemilinear (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k) :
    IsSemilinearWith (semilinPerm A σ) σ := by
  intro c w
  have h : (fun i => σ ((c • w) i)) = σ c • (fun i => σ (w i)) := by
    funext i; simp
  rw [semilinPerm_apply, semilinPerm_apply, h]
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def]
  simp [Matrix.mulVec_smul]

@[expose] def slPerm (k : Type*) [Field k] : SpecialLinearGroup (Fin 2) k →* Equiv.Perm (Fin 2 → k) :=
  MulAction.toPermHom (SpecialLinearGroup (Fin 2) k) (Fin 2 → k)

theorem slPerm_apply (A : SpecialLinearGroup (Fin 2) k) (w : Fin 2 → k) :
    slPerm k A w = A • w := rfl

theorem slPerm_eq_semilinPerm (A : SpecialLinearGroup (Fin 2) k) :
    slPerm k A = semilinPerm A 1 := rfl

theorem slPerm_mem_Gamma (A : SpecialLinearGroup (Fin 2) k) : slPerm k A ∈ Gamma k :=
  semilinPerm_mem A 1

theorem eq_one_of_forall_smul_vec {g : SpecialLinearGroup (Fin 2) k}
    (hall : ∀ w : Fin 2 → k, g • w = w) : g = 1 := by
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  rw [Matrix.SpecialLinearGroup.smul_def] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

theorem slPerm_injective : Function.Injective (slPerm k) := by
  intro A B h
  have hall : ∀ w : Fin 2 → k, (A⁻¹ * B) • w = w := fun w => by
    have h1 : A • w = B • w := congrArg (fun e : Equiv.Perm (Fin 2 → k) => e w) h
    rw [mul_smul, ← h1, inv_smul_smul]
  have := eq_one_of_forall_smul_vec hall
  exact inv_mul_eq_one.mp this

theorem exists_sigma (g : Gamma k) : ∃ σ : k ≃+* k, IsSemilinearWith (g : Equiv.Perm (Fin 2 → k)) σ := by
  obtain ⟨A, σ, hg⟩ := g.2
  exact ⟨σ, hg ▸ semilinPerm_isSemilinear A σ⟩

@[expose] noncomputable def sigmaOf (g : Gamma k) : k ≃+* k := Classical.choose (exists_sigma g)

theorem isSemilinear_sigmaOf (g : Gamma k) :
    IsSemilinearWith (g : Equiv.Perm (Fin 2 → k)) (sigmaOf g) :=
  Classical.choose_spec (exists_sigma g)

theorem sigmaOf_unique {g : Gamma k} {σ : k ≃+* k}
    (h : IsSemilinearWith (g : Equiv.Perm (Fin 2 → k)) σ) : σ = sigmaOf g :=
  h.unique (isSemilinear_sigmaOf g)

@[expose] noncomputable def gammaField (k : Type*) [Field k] : Gamma k →* (k ≃+* k) where
  toFun := sigmaOf
  map_one' := by
    symm
    exact sigmaOf_unique (g := 1) (σ := 1) IsSemilinearWith.one_perm
  map_mul' g h := by
    symm
    exact sigmaOf_unique (g := g * h)
      (σ := sigmaOf g * sigmaOf h) ((isSemilinear_sigmaOf g).mul (isSemilinear_sigmaOf h))

theorem gammaField_apply (g : Gamma k) : gammaField k g = sigmaOf g := rfl

theorem isSemilinear_gammaField (g : Gamma k) :
    IsSemilinearWith (g : Equiv.Perm (Fin 2 → k)) (gammaField k g) := isSemilinear_sigmaOf g

theorem gammaField_semilinPerm (A : SpecialLinearGroup (Fin 2) k) (σ : k ≃+* k) :
    gammaField k ⟨semilinPerm A σ, semilinPerm_mem A σ⟩ = σ :=
  (sigmaOf_unique (g := ⟨semilinPerm A σ, semilinPerm_mem A σ⟩) (semilinPerm_isSemilinear A σ)).symm

@[expose] noncomputable def slGamma (k : Type*) [Field k] : Subgroup (Gamma k) := (gammaField k).ker

theorem mem_slGamma_iff {g : Gamma k} :
    g ∈ slGamma k ↔ ∃ A : SpecialLinearGroup (Fin 2) k, (g : Equiv.Perm (Fin 2 → k)) = slPerm k A := by
  constructor
  · intro hg
    obtain ⟨A, σ, hA⟩ := g.2
    have h1 : gammaField k g = 1 := hg
    have h2 : σ = sigmaOf g := sigmaOf_unique (hA ▸ semilinPerm_isSemilinear A σ)
    have h3 : σ = 1 := by rw [h2]; exact h1
    exact ⟨A, by rw [hA, h3]; rfl⟩
  · rintro ⟨A, hA⟩
    show gammaField k g = 1
    symm
    exact sigmaOf_unique (g := g) (σ := 1) (by rw [hA]; exact semilinPerm_isSemilinear A 1)

theorem slPerm_mem_slGamma (A : SpecialLinearGroup (Fin 2) k) :
    (⟨slPerm k A, slPerm_mem_Gamma A⟩ : Gamma k) ∈ slGamma k :=
  mem_slGamma_iff.mpr ⟨A, rfl⟩

@[expose] noncomputable def slGammaEquiv (k : Type*) [Field k] :
    SpecialLinearGroup (Fin 2) k ≃* slGamma k :=
  MulEquiv.ofBijective
    (((slPerm k).codRestrict (Gamma k) slPerm_mem_Gamma).codRestrict (slGamma k)
      slPerm_mem_slGamma)
    ⟨fun A B h => slPerm_injective
        (congrArg (fun g : slGamma k => ((g : Gamma k) : Equiv.Perm (Fin 2 → k))) h),
     fun g => by
       obtain ⟨A, hA⟩ := mem_slGamma_iff.mp g.2
       exact ⟨A, Subtype.ext (Subtype.ext hA.symm)⟩⟩

theorem slGammaEquiv_apply (A : SpecialLinearGroup (Fin 2) k) :
    (((slGammaEquiv k A : slGamma k) : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k A := rfl

theorem Gamma_apply_zero {g : Equiv.Perm (Fin 2 → k)} (hg : g ∈ Gamma k) : g 0 = 0 := by
  obtain ⟨A, σ, rfl⟩ := hg
  exact (semilinPerm_isSemilinear A σ).map_zero

theorem Gamma_apply_add {g : Equiv.Perm (Fin 2 → k)} (hg : g ∈ Gamma k) (x y : Fin 2 → k) :
    g (x + y) = g x + g y := by
  obtain ⟨A, σ, rfl⟩ := hg
  exact semilinPerm_add A σ x y

@[expose] def rootPerm (ℓ : ℙ k (Fin 2 → k)) : Subgroup (Equiv.Perm (Fin 2 → k)) :=
  (rootGrp ℓ).map (slPerm k)

theorem rootPerm_le_Gamma (ℓ : ℙ k (Fin 2 → k)) : rootPerm ℓ ≤ Gamma k := by
  rintro _ ⟨A, -, rfl⟩
  exact slPerm_mem_Gamma A

theorem mem_rootPerm {ℓ : ℙ k (Fin 2 → k)} {g : Equiv.Perm (Fin 2 → k)} :
    g ∈ rootPerm ℓ ↔ ∃ A ∈ rootGrp ℓ, slPerm k A = g := Iff.rfl

end Gamma

end CFSG.QuasithinUnique.Setup.Campbell
